module Homogeneous.Variety
    (
    -- * Variety
    , Variety (..)
    , Law (..)
    , allLaws
    , subVars

    -- ** Common laws
    , Op0
    , Op1
    , Op2
    , commutative
    , associative
    , idempotent
    , identity_left
    , identity_right

    -- ** Printing laws
    , printAllLaws
    , printLaws
    , printLaw

    -- ** Evaluating laws
    , Testable

    -- *** Exact
    , runTests
    , runAllTests

    , law2property
    , class2quickcheck

    , law2tasty
    , class2tasty
    , superclasses2tasty

    -- *** Approximate
    , isNeighbor
    , Approximate (..)
    )
    where

import Prelude
import Control.Monad
import Data.List
import Data.Foldable
import Data.Typeable

import Data.Kind
import GHC.Exts hiding (IsList(..))

import Test.Tasty
import Test.Tasty.Ingredients.Basic
import Test.Tasty.Options
import Test.Tasty.Runners
-- import qualified Test.Tasty.SmallCheck as SC
import qualified Test.Tasty.QuickCheck as QC
import Test.QuickCheck hiding (Testable)

import TemplateHaskellUtils
import Language.Haskell.TH hiding (Type)
import qualified Language.Haskell.TH as TH

--------------------
data Law alg = Law
    { lawName :: String
    , lhs :: AST alg Var
    , rhs :: AST alg Var
    }

deriving instance Show (AST alg Var) => Show (Law alg)

embedLaw :: View alg1 alg2 => Law alg1 -> Law alg2
embedLaw law = law
    { lhs = embedHomAST $ lhs law
    , rhs = embedHomAST $ rhs law
    }

embedLaws :: View alg1 alg2 => [Law alg1] -> [Law alg2]
embedLaws = map embedLaw


type Op0 alg = AST alg Var
type Op1 alg = AST alg Var -> AST alg Var
type Op2 alg = AST alg Var -> AST alg Var -> AST alg Var

commutative :: Op2 alg -> Law alg
commutative f = Law
    { lawName = "commutative"
    , lhs = f var1 var2
    , rhs = f var2 var1
    }

associative :: Op2 alg -> Law alg
associative f = Law
    { lawName = "associative"
    , lhs = (var1 `f`  var2) `f` var3
    , rhs =  var1 `f` (var2  `f` var3)
    }

idempotent :: Op2 alg -> Law alg
idempotent f = Law
    { lawName = "idempotent"
    , lhs = f var1 var1
    , rhs = var1
    }

identity_left :: Op0 alg -> Op2 alg -> Law alg
identity_left f0 f2 = Law
    { lawName = "identity_left"
    , lhs = f2 f0 var1
    , rhs = var1
    }

identity_right :: Op0 alg -> Op2 alg -> Law alg
identity_right f0 f2 = Law
    { lawName = "identity_right"
    , lhs = f2 var1 f0
    , rhs = var1
    }

--------------------

class (FAlgebra alg, ListLaws alg (AncestorClasses alg)) => Variety alg where
    laws :: [Law alg]

class Variety alg => ListLaws alg (xs::[Type -> Constraint]) where
    listLaws :: Proxy xs -> [(TypeRep,[Law alg])]

instance Variety alg => ListLaws alg '[] where
    listLaws _ = []

instance
    ( Variety alg
    , Variety x
    , View x alg
    , ListLaws alg xs
    ) => ListLaws alg (x ': xs)
        where
    listLaws _ =
        [ (typeRep (Proxy::Proxy x), embedLaws (laws::[Law x])) ]
        ++ listLaws (Proxy::Proxy xs)

allLaws :: forall alg. ListLaws alg (AncestorClasses alg) => [(TypeRep,[Law alg])]
allLaws = listLaws (Proxy::Proxy (AncestorClasses alg))

--------------------------------------------------------------------------------

printAllLaws :: forall alg.
    ( Variety alg
    , Show (AST alg Var)
    ) => IO ()
printAllLaws = do
    forM (allLaws @alg) $ \(t,laws) -> do
        putStrLn $ show t
        forM laws $ \law -> do
            printLaw law

    putStrLn $ show $ typeRep (Proxy::Proxy alg)
    printLaws (Proxy::Proxy alg)
    putStrLn ""

printLaws :: forall alg.
    ( Variety alg
    , Show (AST alg Var)
    ) => Proxy alg -> IO ()
printLaws palg = do
    forM_ (laws::[Law alg]) printLaw

printLaw :: Show (AST alg Var) => Law alg -> IO ()
printLaw law = do
    putStrLn $ "  "++lawName law++":"
    putStrLn $ "    lhs: "++show (lhs law)
    putStrLn $ "    rhs: "++show (rhs law)

----------------------------------------

type Testable a = (Eq a, Arbitrary a, Typeable a)

subVars :: FAlgebra alg => AST alg Var -> [(Var,a)] -> AST alg a
subVars expr varmap = fmap go expr
    where
        go var = case lookup var varmap of
            Just a -> a

law2property :: forall (a :: Type) alg.
    ( FAlgebra alg
    , alg a
    , Eq a
    , Arbitrary a
    ) => Proxy a -> Law alg -> Gen Bool
law2property p law = do
    as <- infiniteListOf (arbitrary::Gen a)
    let varmap = zip (toList (lhs law) ++ toList (rhs law)) as
    return $ (runAST $ subVars (lhs law) varmap)
          == (runAST $ subVars (rhs law) varmap)

class2quickcheck :: forall a alg.
    ( Variety alg
    , alg a
    , Eq a
    , Arbitrary a
    ) => Proxy a -> Proxy alg -> IO ()
class2quickcheck pa _ = forM_ (laws::[Law alg]) $ \law -> do
    putStr $ lawName law++": "
    quickCheck $ law2property pa law

law2tasty :: forall (a :: Type) alg.
    ( FAlgebra alg
    , alg a
    , Testable a
    ) => Proxy a -> Law alg -> TestTree
law2tasty p law = QC.testProperty (lawName law) $ law2property p law

class2tasty :: forall alg a.
    ( Variety alg
    , alg a
    , Testable a
    ) => Proxy alg -> Proxy a -> TestTree
class2tasty palg pa = testGroup
    ( show (typeRep palg) ++ " on " ++ show (typeRep pa) )
    $ map (law2tasty pa) (laws::[Law alg])

superclasses2tasty :: forall alg a.
    ( Variety alg
    , alg a
    , Testable a
    ) => Proxy alg -> Proxy a -> TestTree
superclasses2tasty palg pa = testGroup
    ( show (typeRep palg) ++ " (and superclasses) on " ++ show (typeRep pa) )
    $
    [ testGroup (show t) $ map (law2tasty pa) (laws::[Law alg])
    | (t,laws) <- allLaws @alg
    ]
    ++
    [ class2tasty palg pa
    ]

runTests :: forall alg a.
    ( Variety alg
    , alg a
    , Testable a
    ) => IO ()
runTests = runTasty (class2tasty (Proxy::Proxy alg) (Proxy::Proxy a))

runAllTests :: forall alg a.
    ( Variety alg
    , alg a
    , Testable a
    ) => IO ()
runAllTests = runTasty (superclasses2tasty (Proxy::Proxy alg) (Proxy::Proxy a))

runTasty :: TestTree -> IO ()
runTasty tt = do
    case tryIngredients [consoleTestReporter] (singleOption (HideSuccesses True)) tt of
        Just x -> x
    return ()

--------------------------------------------------------------------------------

isNeighbor :: (Num a, Ord a) => a -> a -> a -> Bool
isNeighbor a1 a2 n = abs (a1-a2) <= n

class (alg a, Variety alg) => Approximate alg a where
    lawError :: Law alg -> [a] -> a

-- instance {-#OVERLAPPABLE#-} (alg a, Variety alg) => Approximate alg a


--------------------------------------------------------------------------------

class (alg1 a, alg2 a) => And (alg1 :: Type -> Constraint) (alg2 :: Type -> Constraint) (a:: Type)
instance (alg1 a, alg2 a) => And alg1 alg2 a

instance (FAlgebra alg1, FAlgebra alg2) => FAlgebra (And alg1 alg2) where
    type ParentClasses (And alg1 alg2) = ParentClasses alg1++ParentClasses alg2
    data Sig (And alg1 alg2) a where
        Sig_And_alg1 :: Sig alg1 a -> Sig (And alg1 alg2) a
        Sig_And_alg2 :: Sig alg2 a -> Sig (And alg1 alg2) a
    runSig (Sig_And_alg1 s) = runSig s
    runSig (Sig_And_alg2 s) = runSig s

instance (Functor (Sig alg1), Functor (Sig alg2)) => Functor (Sig (And alg1 alg2)) where
    fmap f (Sig_And_alg1 s) = Sig_And_alg1 (fmap f s)
    fmap f (Sig_And_alg2 s) = Sig_And_alg2 (fmap f s)

instance (Foldable (Sig alg1), Foldable (Sig alg2)) => Foldable (Sig (And alg1 alg2)) where
    foldr f b (Sig_And_alg1 s) = foldr f b s
    foldr f b (Sig_And_alg2 s) = foldr f b s

instance
    ( Variety alg1
    , Variety alg2
    , ListLaws (And alg1 alg2) (AncestorClasses (And alg1 alg2))
    ) => Variety (And alg1 alg2) where
    laws=[]

-- NOTE:
-- We can't actually make expressions that use both alg1 and alg2 because of this class instance.
-- We need overlapping instances based on differing class constraints,
-- which isn't implemented in GHC.
instance (FAlgebra alg2, View alg' alg1) => View alg' (And alg1 alg2) where
    embedSig = Sig_And_alg1 . embedSig
    unsafeExtractSig (Sig_And_alg1 s) = unsafeExtractSig s

instance
    ( Show (Sig alg1 a)
    , Show (Sig alg2 a)
    ) => Show (Sig (And alg1 alg2) a)
        where
    show (Sig_And_alg1 s) = show s
    show (Sig_And_alg2 s) = show s
