{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}

module Homoiconic.Homogeneous
    (

    -- * FAlgebra
      FAlgebra(..)
    , Free(..)
    , AST
    , runAST
    , View(..)

    -- ** Variables
    , Var
    , mkExprVar
    , var1
    , var2
    , var3

    -- ** Template Haskell
    , mkFAlgebra
    )
where

import           Homoiconic.Homogeneous.TH

import           Prelude
import           Control.Monad
import           Data.List
import           Data.Foldable
import           Data.Typeable

import           Data.Kind
import           GHC.Exts                hiding ( IsList(..) )

--------------------------------------------------------------------------------

class
    ( Functor (Sig alg)
    , Foldable (Sig alg)
    , Typeable alg
    ) => FAlgebra (alg :: Type -> Constraint)
        where
    type ParentClasses alg :: [Type -> Constraint]
    data Sig alg a
    runSig :: alg a => Sig alg a -> a

----------------------------------------

type AncestorClasses alg = Nub (AncestorClasses_ (ParentClasses alg))

type family AncestorClasses_ (xs::[Type -> Constraint]) :: [Type -> Constraint] where
    AncestorClasses_ (x ': xs) = x ': (AncestorClasses_ (ParentClasses x) ++ AncestorClasses_ xs)
    AncestorClasses_ '[] = '[]

type family (++) (xs1:: [x]) (xs2:: [x]) :: [x] where
    '[] ++ '[] = '[]
    '[] ++ xs2 = xs2
    xs1 ++ '[] = xs1
    (x ': xs1) ++ xs2 = x ': (xs1++xs2)

type family Nub xs where
    Nub '[] = '[]
    Nub (x ': xs) = x ': Nub (Remove x xs)

type family Remove x xs where
    Remove x '[]       = '[]
    Remove x (x ': ys) =      Remove x ys
    Remove x (y ': ys) = y ': Remove x ys

----------------------------------------

data Free (f :: Type -> Type) (a :: Type) where
    Free ::f (Free f a) -> Free f a
    Pure ::a -> Free f a

deriving instance (Eq a, Eq (f (Free f a))) => Eq (Free f a)

instance (Show a, Show (f (Free f a))) => Show (Free f a) where
    show (Pure a) = show a
    show (Free f) = "(" ++ show f ++ ")"

instance Functor f => Functor (Free f) where
    fmap g (Free f) = Free (fmap (fmap g) f)
    fmap g (Pure a) = Pure (g a)

instance (Functor f, Foldable f) => Foldable (Free f) where
    foldMap f (Free fa) = fold $ fmap (foldMap f) fa
    foldMap f (Pure a ) = f a

type AST (alg :: Type -> Constraint) a = Free (Sig alg) a

{-# INLINABLE runAST #-}
runAST :: (FAlgebra alg, alg a) => AST alg a -> a
runAST (Pure a) = a
runAST (Free f) = runSig (fmap runAST f)

class (FAlgebra alg1, FAlgebra alg2) => View alg1 alg2 where
    embedSig         :: Sig alg1 a -> Sig alg2 a
    unsafeExtractSig :: Sig alg2 a -> Sig alg1 a

instance FAlgebra alg => View alg alg where
    embedSig         = id
    unsafeExtractSig = id

embedHomAST :: View alg1 alg2 => AST alg1 a -> AST alg2 a
embedHomAST (Free f) = Free $ embedSig $ fmap embedHomAST f
embedHomAST (Pure a) = Pure a

----------------------------------------

newtype Var = Var String
    deriving (Eq)

instance Show Var where
    show (Var v) = v

mkExprVar :: String -> AST alg Var
mkExprVar str = Pure $ Var str

var1 :: AST alg Var
var1 = Pure $ Var "var1"

var2 :: AST alg Var
var2 = Pure $ Var "var2"

var3 :: AST alg Var
var3 = Pure $ Var "var3"

--------------------------------------------------------------------------------
-- generate instances for the Prelude's hierarchy using template haskell

mkFAlgebra ''Num
mkFAlgebra ''Fractional
mkFAlgebra ''Floating
-- mkFAlgebra ''Eq
instance FAlgebra Eq
instance Functor (Sig Eq)
instance Foldable (Sig Eq)
instance Show (Sig Eq a)
instance Eq (Sig Eq a)
mkFAlgebra ''Ord

class (Floating a, Ord a) => FloatingOrd a
instance {-#OVERLAPPABLE#-} (Floating a, Ord a) => FloatingOrd a
mkFAlgebra ''FloatingOrd

