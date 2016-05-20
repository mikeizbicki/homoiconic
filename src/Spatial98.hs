{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoRebindableSyntax #-}

module Spatial98
    where

import Prelude (fromInteger, Bool(..), Monad(..))
import qualified Prelude as P
import Data.Foldable
import Data.List
import Data.Typeable

import LocalPrelude
import Lattice
import Topology
import FAlgebra98

import Test.Tasty
import Test.Tasty.Ingredients.Basic
import Test.Tasty.Options
import Test.Tasty.Runners
import qualified Test.Tasty.SmallCheck as SC
import qualified Test.Tasty.QuickCheck as QC
import Test.QuickCheck hiding (Testable)

import Debug.Trace

--------------------------------------------------------------------------------

data EpsLaw (alg :: * -> Constraint) a = EpsLaw
    { epsLawName :: String
    , epsilon :: [a] -> Neighborhood a
    }

class (Variety98 alg, alg a, Topology a) => Approximate98 alg a where
    epsLaws :: [EpsLaw alg a]

instance {-#OVERLAPPABLE#-} (Variety98 alg, alg a, Topology a) => Approximate98 alg a where
    epsLaws = []

--------------------------------------------------------------------------------

lookupEpsLaw :: forall alg a.
    ( Approximate98 alg a
    ) => String
      -> EpsLaw alg a
lookupEpsLaw lawName = case lookup lawName lawmap of
    Just x -> x
    Nothing -> EpsLaw lawName lowerBound
    where
        lawmap = map (\x -> (epsLawName x,x)) (epsLaws::[EpsLaw alg a])

epsLaw2quickcheck :: forall (a :: *) alg.
    ( Variety98 alg
    , alg a
    , Testable98 a
    , Topology a
    ) => Proxy a -> Law alg -> TestTree
epsLaw2quickcheck p law = QC.testProperty (lawName law) $ do
    as <- infiniteListOf (arbitrary::Gen a)
    let eps = epsilon (lookupEpsLaw $ lawName law :: EpsLaw alg a) as
    return $ checkApproximate as law eps

checkApproximate ::
    ( Approximate98 alg a
    , Testable98 a
    ) => [a] -> Law alg -> Logic a
checkApproximate as law
    = (eval98 $ subVars (lhs law) varmap)
   == (eval98 $ subVars (rhs law) varmap)
    where
        varmap = zip (toList (lhs law) ++ toList (rhs law)) as

approxclass2tasty :: forall alg a.
    ( Variety98 alg
    , alg a
    , Testable98 a
    , Topology a
    ) => Proxy alg -> Proxy a -> TestTree
approxclass2tasty palg pa = testGroup
    ( show (typeRep palg) ++ " on " ++ show (typeRep pa) )
    $ map (epsLaw2quickcheck pa) (laws::[Law alg])

-- runTestsApprox :: forall alg a.
--     ( Variety98 alg
--     , alg a
--     , Testable98 a
--     , Topology a
--     ) => Proxy alg -> Proxy a -> IO ()
-- -- runTestsApprox _ _ = return ()
-- runTestsApprox = runTasty (approxclass2tasty (Proxy::Proxy alg) (Proxy::Proxy a))

runTasty :: TestTree -> IO ()
runTasty tt = do
    case tryIngredients [consoleTestReporter] (singleOption (HideSuccesses True)) tt of
        Just x -> x
    return ()

instance LowerBounded a => Show (a -> Bool) where
    show f = show $ f lowerBound

