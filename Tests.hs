{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveGeneric #-}

module Tests
    where

import qualified Prelude as P
import LocalPrelude
import Lattice
import Union
import Topology1 hiding (Lawful (..), Semigroup (..), isLawful)

import Data.Typeable
import Test.SmallCheck.Series
import Test.Tasty
import Test.Tasty.Ingredients.Basic
import qualified Test.Tasty.SmallCheck as SC
import qualified Test.Tasty.QuickCheck as QC
import Test.QuickCheck hiding (Testable)

import Debug.Trace

--------------------------------------------------------------------------------

type LawName = String

class Lawful (cxt :: * -> Constraint) where
    laws :: (Approximate cxt a, Testable a, cxt a) => Proxy cxt -> Proxy a -> [Law cxt a]

data Law cxt a where
    Law :: Testable p => LawName -> (p -> Bool) -> Law cxt a
--     Law :: (Approximate cxt a, Testable p) => LawName -> (p -> Bool) -> Law cxt a
--     Law :: (Approximate cxt a, Testable p) => LawName -> (p -> Logic a) -> Law cxt a
--     Law :: Testable p => LawName -> (p -> Logic a) -> Law a

type Testable p = (Show p, Arbitrary p, CoArbitrary p, Serial IO p, Typeable p)
-- type Testable p = (Show p, Arbitrary p, CoArbitrary p, SC.Testable IO p, QC.Testable p)

--------------------

mkLaw :: forall p cxt a.
    ( Testable p
    , Approximate cxt a
    ) => LawName
      -> (p -> Logic a)
      -> Law cxt a
-- mkLaw law f = Law law ( \p -> f p lowerBound )
mkLaw lawname f = Law lawname ( \p -> f p $ bound p)
    where
--         bound = lowerBound
        bound = case getMaxUnlawful (Proxy::Proxy cxt) (Proxy::Proxy a) lawname of
            Just a -> a
--             Nothing -> error "blah"

--------------------

data ErrorBound a where
    ErrorBound :: (Typeable (Neighborhood a), Testable p) => LawName -> (p -> Neighborhood a) -> ErrorBound a
--     ErrorBound :: LawName -> Neighborhood a -> ErrorBound a

-- FIXME: the types are mildly broken for Topology2 above; this code partially fixes it
class (Lawful cxt, Topology a, cxt a) => Approximate cxt a where
    maxUnlawful :: cxt a => Proxy cxt -> Proxy a -> [ ErrorBound a ]

instance {-# OVERLAPPABLE #-} (Lawful cxt, Topology a, cxt a) => Approximate cxt a where
    maxUnlawful _ _ = []

instance {-# OVERLAPS #-}
    ( Approximate cxt a
    , Approximate cxt b
    , Typeable (Neighborhood a)
    , Typeable (Neighborhood b)
    , cxt (a,b)
    ) => Approximate cxt (a,b) where

    maxUnlawful p1 _ = go
        (maxUnlawful p1 (Proxy::Proxy a))
        (maxUnlawful p1 (Proxy::Proxy b))
        where
            go as@(ErrorBound lawa na:ar) bs@(ErrorBound lawb nb:br) = case P.compare lawa lawb of
--                 P.EQ -> ErrorBound lawa (\p -> (na p,nb p)):go ar br
                P.LT -> ErrorBound lawa (\p -> (na p,lowerBound)):go ar bs
                P.GT -> ErrorBound lawa (\p -> (lowerBound,nb p)):go as br

            go (ErrorBound lawa na:ar) [] = ErrorBound lawa (\p -> (na p,lowerBound)):go ar []
            go [] (ErrorBound lawb nb:br) = ErrorBound lawb (\p -> (lowerBound,nb p)):go [] br
            go [] [] = []

getMaxUnlawful :: forall p cxt a. (Testable p, Approximate cxt a)
    => Proxy (cxt :: * -> Constraint)
    -> Proxy a
    -> LawName
    -> Maybe (p -> Neighborhood a)
getMaxUnlawful pcxt pa lawWanted = go $ maxUnlawful pcxt pa
    where
        go [] = Just lowerBound
        go (ErrorBound law a:xs) = if law==lawWanted
            then trace ("\ntypeRep="++show (typeRep (Proxy::Proxy (p -> Neighborhood a))))
               $ trace ("\ntypeOf="++show (typeOf a))
               $ cast a
            else go xs

--------------------------------------------------------------------------------

isLawful :: forall cxt a. (Testable a, Approximate cxt a) => Proxy cxt -> Proxy a -> IO ()
isLawful pcxt pa = defaultMain
    $ localOption (QC.QuickCheckTests 100)
    $ localOption (SC.SmallCheckDepth 3)
    $ testGroup "isLaw" $ concat $ map go $ laws pcxt pa
    where
--         go _ = []
--         go (Law _ _ ) = []
--         go (Law name prop) = []
        go (Law name prop) =
            [ QC.testProperty (name++" (QuickCheck)") prop
--             , SC.testProperty (name++" (SmallCheck)") prop
            ]
--         go (Law name prop) =
--             [ QC.testProperty (name++" (QuickCheck)") (\p -> prop p bound)
--             , SC.testProperty (name++" (SmallCheck)") (\p -> prop p bound)
--             ]
--             where
--                 bound = getMaxUnlawful pcxt pa name

