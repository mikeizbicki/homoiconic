{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Algebra6
    where

import LocalPrelude
import Prelude (Functor(..), Applicative(..), Monad(..))
import qualified Prelude as P

--------------------------------------------------------------------------------

class Semigroup a where
    (+) :: a -> a -> a

class Semigroup a => Monoid a where
    zero :: a

class Monoid a => Group a where
    negate :: a -> a
    (-) :: a -> a -> a

class (Group a, Module (Scalar a)) => Module a where
--     type Scalar a = r | r -> a
    type Scalar a
    (*) :: Scalar a -> a -> a

class Module a => Hilbert a where
    (<>) :: a -> a -> Scalar a

----------------------------------------

instance Semigroup Int where (+) = (P.+)
instance Monoid Int where zero = 0
instance Group Int where negate = P.negate; (-) = (P.-)
instance Module Int where
    type Scalar Int = Int
    (*) = (P.*)
instance Hilbert Int where
    (<>) = (P.*)

instance (Semigroup a, Semigroup b) => Semigroup (a,b) where
    (a1,b1)+(a2,b2) = (a1+a2,b1+b2)
instance (Monoid a, Monoid b) => Monoid (a,b) where
    zero = (zero,zero)
instance (Group a, Group b) => Group (a,b) where
    negate (a,b) = (negate a, negate b)
    (a1,b1)-(a2,b2) = (a1-a2,b1-b2)
instance (Module a, Module b, Scalar a~Scalar b) => Module (a,b) where
    type Scalar (a,b) = Scalar b
    s*(a,b) = (s*a,s*b)
instance (Hilbert a, Hilbert b, Scalar a~Scalar b) => Hilbert (a,b) where
    (a1,b1)<>(a2,b2) = (a1<>a2)+(b1<>b2)

--------------------------------------------------------------------------------

data Free (f::Type->Type) (a::Type) where
    Free     :: f            (Free f a)  -> Free f a
    Pure     :: a -> Free f a

instance
    ( Show a
    , Show (f (Free f a))
--     , Show (f (BoxScalar (Free f a)))
    ) => Show (Free f a)
        where
--     show (FreeBox2 f) = show f
--     show (FreeSca f) = show f
    show (Free    f) = show f
    show (Pure    a) = show a

instance Functor f => Functor (Free f) where
    fmap g (Free f) = Free (fmap (fmap g) f)
    fmap g (Pure a) = Pure $ g a

----------------------------------------

type Expr alg a = Free (Sig alg) a

eval :: (FAlgebra alg, alg a) => Expr alg a -> a
eval (Free f) = alg $ fmap eval f
eval (Pure a) = a

type Space = Hilbert

x :: Expr Space (Int,Int)
x = Pure (2,2)

y :: Expr Space (Int,Int)
y = Pure (1,3)

z :: Expr Space (Int,Int)
z = Pure (1,2)

--------------------------------------------------------------------------------

class Functor (Sig alg) => FAlgebra (alg::Type->Constraint) where
    data Sig alg a
    alg :: alg a => Sig alg a -> a

class FAlgebra alg => Variety alg where
    laws :: [Law alg]

data Law (alg::Type->Constraint) = Law
    { name :: String
    , lhs :: Expr alg String
    , rhs :: Expr alg String
    }

----------------------------------------

instance FAlgebra Module where
    data Sig Module a where
        SGM :: Sig Group a -> Sig Module a
        SGp :: Scalar a -> a -> Sig Module a
    alg (SGM g) = alg g
    alg (SGp s a) = s*a

instance (Show (Scalar a), Show a) => Show (Sig Module a) where
    show (SGM g) = show g
    show (SGp s a) = "("++show s++"*"++show a++")"

instance Functor (Sig Module) where
    fmap f (SGM g) = SGM $ fmap f g
    fmap f (SGp s a) = SGp (error "scalar") (f a)

instance Semigroup (Expr Module a) where
    (+) e1 e2 = Free $ SGM $ SG $ SM $ Sp e1 e2

instance Monoid (Expr Module a) where
    zero = Free $ SGM $ SG $ Sz

instance Group (Expr Module a) where
    negate e = Free $ SGM $ Sn e
    (-) e1 e2 = Free $ SGM $ Sm e1 e2

instance Module (Expr Module a) where
    type Scalar (Expr Module a) = Expr Module (Scalar a)
    (*) e1 e2 = Free $ SGp e1 e2

----------------------------------------

instance FAlgebra Hilbert where
    data Sig Hilbert a where
        SH :: Sig Module a -> Sig Hilbert a
        Sd :: a -> a -> Sig Hilbert (BoxScalar a)
    alg (SH h) = alg h
--     alg (Sd a1 a2) = BoxScalar $ a1<>a2

instance
    ( Show a
    , Show (Scalar a)
    ) => Show (Sig Hilbert a) where
    show (SH h) = show h

-- instance {-#OVERLAPS#-}
--     ( Show a
--     , Show (BoxScalar a)
--     , Show (Scalar (BoxScalar a))
--     ) => Show (Sig Hilbert (BoxScalar a)) where
--     show (SH h) = show h
--     show (Sd a1 a2) = "("++show a1++"<>"++show a2++")"

instance Functor (Sig Hilbert) where
    fmap f (SH h) = SH $ fmap f h

--------------------

instance Semigroup (Expr Hilbert a) where
    (+) e1 e2 = Free $ SH $ SGM $ SG $ SM $ Sp e1 e2

instance Monoid (Expr Hilbert a) where
    zero = Free $ SH $ SGM $ SG $ Sz

instance Group (Expr Hilbert a) where
    negate e = Free $ SH $ SGM $ Sn e
    (-) e1 e2 = Free $ SH $ SGM $ Sm e1 e2

instance Module (Expr Hilbert a) where
--     type Scalar (Expr Hilbert a) = Expr Hilbert (BoxScalar a)
--     type Scalar (Expr Hilbert a) = BoxScalar (Expr Hilbert a)
    type Scalar (Expr Hilbert a) = Expr Hilbert (Scalar a)
    (*) e1 e2 = Free $ SH $ SGp e1 e2

instance Hilbert (Expr Hilbert a) where
--     (<>) e1 e2 = FreeSca $ Sd e1 e2

--------------------

newtype BoxScalar a = BoxScalar (Scalar a)

instance Module a => Semigroup (BoxScalar a) where
    (+) (BoxScalar a1) (BoxScalar a2) = BoxScalar $ a1+a2

instance Module a => Monoid (BoxScalar a) where
    zero = BoxScalar zero

instance Module a => Group (BoxScalar a) where
    negate (BoxScalar a) = BoxScalar (negate a)
    (-) (BoxScalar a1) (BoxScalar a2) = BoxScalar (a1-a2)

instance Module a => Module (BoxScalar a) where
    type Scalar (BoxScalar a) = BoxScalar (Scalar a)
    (*) (BoxScalar s) (BoxScalar a) = BoxScalar (s*a)

instance Show (Scalar a) => Show (BoxScalar a) where
    show (BoxScalar a) = show a

----------------------------------------

instance FAlgebra Semigroup where
    data Sig Semigroup a where
        Sp :: a -> a -> Sig Semigroup a
    alg (Sp a1 a2) = a1+a2

instance Show a => Show (Sig Semigroup a) where
    show (Sp a1 a2) = "("++show a1++"+"++show a2++")"

instance Functor (Sig Semigroup) where
    fmap f (Sp a1 a2) = Sp (f a1) (f a2)

instance Semigroup (Expr Semigroup a) where
    (+) e1 e2 = Free $ Sp e1 e2

----------------------------------------

instance FAlgebra Monoid where
    data Sig Monoid a where
        SM :: Sig Semigroup a -> Sig Monoid a
        Sz :: Sig Monoid a
    alg (SM m) = alg m
    alg Sz     = zero

instance Show a => Show (Sig Monoid a) where
    show (SM m) = show m
    show Sz = "0"

instance Functor (Sig Monoid) where
    fmap f (SM m) = SM $ fmap f m
    fmap f Sz = Sz

instance Semigroup (Expr Monoid a) where
    (+) e1 e2 = Free $ SM $ Sp e1 e2

instance Monoid (Expr Monoid a) where
    zero = Free $ Sz

----------------------------------------

instance FAlgebra Group where
    data Sig Group a where
        SG :: Sig Monoid a -> Sig Group a
        Sn :: a -> Sig Group a
        Sm :: a -> a -> Sig Group a
    alg (SG g) = alg g
    alg (Sn m) = negate m
    alg (Sm a1 a2) = a1-a2

instance Show a => Show (Sig Group a) where
    show (SG g) = show g
    show (Sn m) = "(-"++show m++")"
    show (Sm a1 a2) = "("++show a1++"-"++show a2++")"

instance Functor (Sig Group) where
    fmap f (SG g) = SG $ fmap f g
    fmap f (Sn m) = Sn $ f m
    fmap f (Sm a1 a2) = Sm (f a1) (f a2)

instance Semigroup (Expr Group a) where
    (+) e1 e2 = Free $ SG $ SM $ Sp e1 e2

instance Monoid (Expr Group a) where
    zero = Free $ SG $ Sz

instance Group (Expr Group a) where
    negate e = Free $ Sn e
    (-) e1 e2 = Free $ Sm e1 e2

--------------------------------------------------------------------------------
