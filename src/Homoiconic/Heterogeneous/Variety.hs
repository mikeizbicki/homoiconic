{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilyDependencies #-}

{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

module Heterogeneous.FAlgebra
    (
    -- *
    , Variety (..)
    , Law (..)
    , Var
    , var1
    , var2
    , var3
    )
    where

import Prelude
import Control.Monad
import Data.Foldable
import Data.List
import Data.Maybe
import Data.Typeable
import Data.Proxy

import Data.Kind
import GHC.Exts hiding (IsList(..))

import Test.Tasty
import Test.Tasty.Ingredients.Basic
import Test.Tasty.Options
import Test.Tasty.Runners
import qualified Test.Tasty.SmallCheck as SC
import qualified Test.Tasty.QuickCheck as QC
import Test.QuickCheck hiding (Testable)

import TemplateHaskellUtils
import Language.Haskell.TH hiding (Type)
import qualified Language.Haskell.TH as TH

import Debug.Trace

import Unsafe.Coerce

--------------------------------------------------------------------------------

data Law alg t = Law
    { lawName :: String
    , lhs :: AST alg t Var
    , rhs :: AST alg t Var
    }

deriving instance Show (AST alg t Var) => Show (Law alg t)

--------------------

-- type Op0 alg = AST alg Var
-- type Op1 alg = AST alg Var -> AST alg Var
-- type Op2 alg = AST alg Var -> AST alg Var -> AST alg Var
--
-- commutative :: Op2 alg -> Law alg
-- commutative f = Law
--     { lawName = "commutative"
--     , lhs = f var1 var2
--     , rhs = f var2 var1
--     }
--
-- associative :: Op2 alg -> Law alg
-- associative f = Law
--     { lawName = "associative"
--     , lhs = (var1 `f`  var2) `f` var3
--     , rhs =  var1 `f` (var2  `f` var3)
--     }
--
-- idempotent :: Op2 alg -> Law alg
-- idempotent f = Law
--     { lawName = "idempotent"
--     , lhs = f var1 var1
--     , rhs = var1
--     }
--
-- identity_left :: Op0 alg -> Op2 alg -> Law alg
-- identity_left f0 f2 = Law
--     { lawName = "identity_left"
--     , lhs = f2 f0 var1
--     , rhs = var1
--     }
--
-- identity_right :: Op0 alg -> Op2 alg -> Law alg
-- identity_right f0 f2 = Law
--     { lawName = "identity_right"
--     , lhs = f2 var1 f0
--     , rhs = var1
--     }

--------------------

-- type family AncestorClasses (t::Type->Constraint) :: [Type -> Constraint]

type ClassSig = (Type->Constraint,[Tag])

type family ParentClasses (alg::ClassSig) :: [ClassSig]

type AncestorClasses alg = Nub (AncestorClasses_ (ParentClasses alg))

type family AncestorClasses_ (xs::[ClassSig]) :: [ClassSig] where
    AncestorClasses_ (x ': xs) = x ': (AncestorClasses_ (ParentClasses x) ++ AncestorClasses_ xs)
    AncestorClasses_ '[] = '[]

-- type family (++) (xs1:: [x]) (xs2:: [x]) :: [x] where
--     '[] ++ '[] = '[]
--     '[] ++ xs2 = xs2
--     xs1 ++ '[] = xs1
--     (x ': xs1) ++ xs2 = x ': (xs1++xs2)

type family Nub xs where
    Nub '[] = '[]
    Nub (x ': xs) = x ': Nub (Remove x xs)

type family Remove x xs where
    Remove x '[]       = '[]
    Remove x (x ': ys) =      Remove x ys
    Remove x (y ': ys) = y ': Remove x ys

--------------------

-- class (FAlgebra alg , ListLaws alg (AncestorClasses '(alg,'[]))) => Variety alg where
class FAlgebra alg => Variety alg where
    laws :: [Law alg '[]]

-- class Variety alg => ListLaws alg (xs::[ClassSig]) where
--     listLaws :: Proxy xs -> [(TypeRep,[Law alg '[]])]
--
-- instance Variety alg => ListLaws alg '[] where
--     listLaws _ = []
--
-- instance
--     ( Variety alg
--     , Variety alg'
--     , View alg' t' alg '[]
--     , ListLaws alg xs
--     , Typeable t'
--     ) => ListLaws alg ( '(alg',t') ': xs)
--         where
--     listLaws _ =
--         [ (typeRep (Proxy::Proxy alg'), embedLaws (laws::[Law alg' t'])) ]
--         ++
--         listLaws (Proxy::Proxy xs)
--
-- allLaws :: forall alg t. ListLaws alg (AncestorClasses '(alg,'[])) => [(TypeRep,[Law alg '[]])]
-- allLaws = listLaws (Proxy::Proxy (AncestorClasses '(alg,'[])))

--------------------

-- embedLaw :: View alg1 t1 alg2 t2 => Law alg1 t1 -> Law alg2 t2
-- embedLaw law = law
--     { lhs = embedAST $ lhs law
--     , rhs = embedAST $ rhs law
--     }
--
-- embedLaws :: View alg1 t1 alg2 t2 => [Law alg1 t1] -> [Law alg2 t2]
-- embedLaws = map embedLaw

--------------------------------------------------------------------------------

-- printAllLaws :: forall alg.
--     ( Variety alg
--     , Show (AST alg Var)
--     ) => IO ()
-- printAllLaws = do
--     forM (allLaws @alg) $ \(t,laws) -> do
--         putStrLn $ show t
--         forM laws $ \law -> do
--             printLaw law
--
--     putStrLn $ show $ typeRep (Proxy::Proxy alg)
--     printLaws (Proxy::Proxy alg)
--     putStrLn ""

printLaws :: forall alg.
    ( Variety alg
    , Show (AST alg '[] Var)
    ) => Proxy alg -> IO ()
printLaws palg = do
    forM_ (laws::[Law alg '[]]) printLaw

printLaw :: Show (AST alg t Var) => Law alg t -> IO ()
printLaw law = do
    putStrLn $ "  "++lawName law++":"
    putStrLn $ "    lhs: "++show (lhs law)
    putStrLn $ "    rhs: "++show (rhs law)

----------------------------------------

type Testable a = (Eq a, Arbitrary a, Typeable a)

-- subVars :: (Functor (Sig alg t), FAlgebra alg) => AST alg t Var -> [(Var,a)] -> AST alg t a
-- subVars expr varmap = fmap go expr
--     where
--         go var = case lookup var varmap of
--             Just a -> a
--
-- law2quickcheck :: forall (a::Type) alg t.
--     ( FAlgebra alg
--     , alg a
--     , Testable a
--     ) => Proxy a -> Law alg t -> TestTree
-- law2quickcheck p law = QC.testProperty (lawName law) $ do
--     as <- infiniteListOf (arbitrary::Gen a)
--     let varmap = zip (toList (lhs law) ++ toList (rhs law)) as
--     return $ (runAST $ subVars (lhs law) varmap)
--           == (runAST $ subVars (rhs law) varmap)

