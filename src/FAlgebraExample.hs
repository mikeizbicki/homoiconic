{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module FAlgebraExample
    where

import Prelude hiding (Monoid (..),(-),(+),negate,(==))
import Data.Foldable
import Data.List
import Data.Typeable
import Data.Proxy
import qualified Prelude as P
-- import GHC.Exts

import FAlgebra
-- import FAlgebra98
-- import Topology
-- import Lattice

--------------------------------------------------------------------------------

class Semigroup a where
    (+) :: a -> a -> a

mkFAlgebra ''Semigroup

-- pattern Expr_plus ::
--     ( View Semigroup '[] alg t
--     , TypeConstraints t a
--     ) => Free (Sig alg) t a
--       -> Free (Sig alg) t a
--       -> Free (Sig alg) t a
-- pattern Expr_plus e1 e2 <- Free (toSigPoset -> Si e1 e2) where
--     Expr_plus e1 e2 = Free $ fromSigPoset $ Si e1 e2

-- instance (View Semigroup '[] alg t, TypeConstraints t a) => Semigroup (Free (Sig alg) t a) where
--     (+) e1 e2 = Free $ embedSig $ Sig_plus e1 e2
--     (+) = Expr_plus

class Semigroup a => Monoid a where
    zero :: a

mkFAlgebra ''Monoid

type family Scalar a
mkAT ''Scalar

type instance Scalar Int = Int
type instance Scalar (Free (Sig alg) t a) = Free (Sig alg) (TScalar ': t) a

-- class (Semigroup a, Monoid a, Semigroup (Scalar a), Monoid (Scalar a)) => Module a where
class (Monoid a, Monoid (Scalar a)) => Module a where
-- class Monoid a => Module a where
    (.*) :: Scalar a -> a -> a

-- instance FAlgebra Module where
--     data Sig Module t a where
--         Sig_dotmul :: Scalar a -> a -> Sig Module '[] a
--
--     mape f (Sig_dotmul a1 a2) = Sig_dotmul (f a1) (f a2)

mkFAlgebra ''Module

type family Foo a
mkAT ''Foo
type instance Foo (Free (Sig alg) t a) = Free (Sig alg) (TFoo ': t) a

-- class (Semigroup a, Monoid a, Semigroup (Scalar a), Monoid (Scalar a), Module a) => Hilbert a where
class Module a => Hilbert a where
--     aaa :: a -> a -> a
    (<>) :: a -> a -> Scalar a
--     asd :: a -> Foo a

mkFAlgebra ''Hilbert

class Hilbert a => Floobert a where
    floo :: a -> a

mkFAlgebra ''Floobert

class Topology a where
    type Logic a
    (==) :: a -> a -> Logic a


-- instance View Topology '[] alg t => Topology (Free (Sig alg) t a) where
--     (==) e1 e2 = Free $ embedSig $ Sig_eqeq

mkFAlgebra ''Topology
-- mkAT ''Logic

--------------------------------------------------------------------------------

type instance TypeConstraints t a = ()

type Space = Hilbert

x :: Free (Sig Space) '[] Int
x = Pure 1

y :: Free (Sig Space) '[TScalar] Int
y = Pure 2
