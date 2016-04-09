module Algebra7
    where

import LocalPrelude
import Prelude (Functor(..), Applicative(..), Monad(..))
import qualified Prelude as P

import GHC.TypeLits

--------------------------------------------------------------------------------

class Topology a where
    type Logic a
    (==) :: a -> a -> Logic a

class Topology a => Semigroup a where
    (+) :: a -> a -> a

class Semigroup a => Module a where
    type family Scalar a
    (.*) :: Scalar a -> a -> a

class Module a => Hilbert a where
    (<>) :: a -> a -> Scalar a


----------------------------------------

instance Topology Int where
    type Logic Int = Bool
    (==) = (P.==)
instance Semigroup Int where (+) = (P.+)
instance Module Int where
    (.*) = (P.*)
    type Scalar Int = Int
instance Hilbert Int where
    (<>) = (P.*)

instance (Topology a, Topology b) => Topology (a,b) where
    type Logic (a,b) = (Logic a, Logic b)
    (a1,b1)==(a2,b2) = (a1==a2,b1==b2)
instance (Semigroup a, Semigroup b) => Semigroup (a,b) where
    (a1,b1)+(a2,b2) = (a1+a2,b1+b2)
instance (Module a, Module b, Semigroup (Scalar b), Scalar a~Scalar b) => Module (a,b) where
    type Scalar (a,b) = Scalar b
    s.*(a,b) = (s.*a,s.*b)
instance (Hilbert a, Hilbert b, Semigroup (Scalar b), Scalar a~Scalar b) => Hilbert (a,b) where
    (a1,b1)<>(a2,b2) = (a1<>a2)+(b1<>b2)

----------------------------------------

type Space = Hilbert

x :: Expr Space 'Id (Int,Int)
x = Pure (2,2)

y :: Expr Space 'Id (Int,Int)
y = Pure (1,3)

z :: Expr Space (Tag 'Scalar 'Id) (Int,Int)
z = Pure 1

--------------------------------------------------------------------------------

data Free (f::AT->Type->Type) (t::AT) (a::Type) where
    FreeTag  :: f (Tag s t) (Free f t a)  -> Free f (Tag s t) a
    Free     :: f        t  (Free f t a)  -> Free f        t  a
    Pure     :: App t a -> Free f t a

instance
    ( Show      (App t a)
    , Show      (f t (Free f t a))
    , ShowUntag (f t (Free f t a))
    ) => Show (Free f t a)
        where
    show (FreeTag f) = show f
    show (Free    f) = show f
    show (Pure    a) = show a

type family ShowUntag (f::Type) :: Constraint where
    ShowUntag (f (Tag s t) (Free f (Tag s t) a))  = Show (f (Tag s t) (Free f t a))
    ShowUntag _ = ()

instance Functor (f t) => Functor (Free f t) where
    fmap g (Free f) = Free (fmap (fmap g) f)
--     fmap g (Pure a) = Pure $ g a

----------------------------------------

type Expr alg t a = Free (Sig alg) t a

-- eval :: (Functor (Sig alg t), FAlgebra alg, alg (App t a)) => Expr alg t a -> App t a
-- eval (FreeTag f) = alg $ fmap eval f
-- eval (Free    f) = alg $ fmap eval f
-- eval (Pure    a) = a

--------------------------------------------------------------------------------

class FAlgebra (alg::Type->Constraint) where
    data Sig alg (t::AT) a
    alg :: alg a => Sig alg t a -> a

----------------------------------------

instance FAlgebra Topology where
    data Sig Topology t a where
        Se :: a -> a -> Sig Topology (Tag 'Logic t) a
--     alg (Se a1 a2) = a1==a2

instance Show a => Show (Sig Topology t a) where
    show (Se a1 a2) = "("++show a1++"=="++show a2++")"

instance Topology (Expr Topology t a) where
    type Logic (Expr Topology t a) = Expr Topology (Tag 'Logic t) a
    (==) e1 e2 = FreeTag $ Se e1 e2

----------------------------------------

instance FAlgebra Semigroup where
    data Sig Semigroup t a where
        SS :: Sig Topology t a -> Sig Semigroup t a
        Sp :: a -> a -> Sig Semigroup t a
    alg (SS s) = alg s
    alg (Sp a1 a2) = a1+a2

instance Show a => Show (Sig Semigroup t a) where
    show (SS s) = show s
    show (Sp a1 a2) = "("++show a1++"+"++show a2++")"

-- instance Functor (Sig Semigroup t) where
--     fmap f (Sp a1 a2) = Sp (f a1) (f a2)

instance Topology (Expr Semigroup t a) where
    type Logic (Expr Semigroup t a) = Expr Semigroup (Tag 'Logic t) a
    (==) e1 e2 = FreeTag $ SS $ Se e1 e2

instance Semigroup (Expr Semigroup t a) where
    (+) e1 e2 = Free $ Sp e1 e2

----------------------------------------

instance FAlgebra Module where
    data Sig Module t a where
        SM :: Sig Semigroup t a -> Sig Module t a
        Sm :: Scalar a -> a -> Sig Module t a
    alg (SM m) = alg m
    alg (Sm s a) = s.*a

instance
    ( Show a
    , Show (Scalar a)
    ) => Show (Sig Module t a)
        where
    show (SM m) = show m
    show (Sm s a) = "("++show s++".*"++show a++")"

instance {-#OVERLAPS#-}
    ( Show a
    ) => Show (Sig Module (Tag 'Scalar (Tag 'Scalar t)) a)
        where
    show (SM m) = show m
    show (Sm s a) = "( <<depth exceeded>>.*"++show a++")"

instance {-#OVERLAPS#-}
    ( Show a
    ) => Show (Sig Module (Tag 'Logic t) a)
        where
    show (SM m) = show m

instance Topology (Expr Module t a) where
    type Logic (Expr Module t a) = Expr Module (Tag 'Logic t) a
    (==) e1 e2 = FreeTag $ SM $ SS $ Se e1 e2

instance Semigroup (Expr Module t a) where
    (+) e1 e2 = Free $ SM $ Sp e1 e2

instance Module (Expr Module t a) where
    type Scalar (Expr Module t a) = Expr Module (Tag 'Scalar t) a
    (.*) e1 e2 = Free $ Sm e1 e2

-- NOTE:
-- This method works great for the Module FALgebra, but it doesn't work for Hilbert.
-- This is because the return type of Sd requires that the 'Scalar tag be appended each time.
--
-- type family ExprModuleScalar a where
--     ExprModuleScalar (Expr Module (Tag 'Scalar t) a) = Expr Module (Tag 'Scalar t) a
--     ExprModuleScalar (Expr Module              t  a) = Expr Module (Tag 'Scalar t) a

----------------------------------------

instance FAlgebra Hilbert where
    data Sig Hilbert t a where
        SH :: Sig Module t a -> Sig Hilbert t a
        Sd :: a
           -> a
           -> Sig Hilbert (Tag 'Scalar t) a

    alg (SH h) = alg h

instance
    ( Show a
    , Show (Scalar a)
    ) => Show (Sig Hilbert t a)
        where
    show (SH h) = show h
    show (Sd a1 a2) = "("++show a1++"<>"++show a2++")"

instance {-#OVERLAPS#-}
    ( Show a
    ) => Show (Sig Hilbert (Tag 'Scalar (Tag 'Scalar t)) a)
        where
    show (SH h) = show h
    show (Sd a1 a2) = "("++show a1++"<>"++show a2++")"

instance {-#OVERLAPS#-}
    ( Show a
    ) => Show (Sig Hilbert (Tag 'Logic t) a)
        where
    show (SH h) = show h

-- instance Functor (Sig Hilbert t) where
--     fmap f (SH h) = SH $ fmap f h

instance Topology (Expr Hilbert t a) where
    type Logic (Expr Hilbert t a) = Expr Hilbert (Tag 'Logic t) a
    (==) e1 e2 = FreeTag $ SH $ SM $ SS $ Se e1 e2

instance Semigroup (Expr Hilbert t a) where
    (+) e1 e2 = Free $ SH $ SM $ Sp e1 e2

instance Module (Expr Hilbert t a) where
    type Scalar (Expr Hilbert t a) = Expr Hilbert (Tag 'Scalar t) a
    (.*) e1 e2 = Free $ SH $ Sm e1 e2

instance Hilbert (Expr Hilbert t a) where
    (<>) e1 e2 = FreeTag $ Sd e1 e2

--------------------------------------------------------------------------------

data AT
    = Id
    | Scalar
    | Logic
    | Tag AT AT

type family App (t::AT) (a::Type) :: Type
type instance App 'Id a = a
type instance App 'Scalar a = Scalar a
type instance App 'Logic  a = Logic  a
type instance App (Tag t t') a = App t (App t' a)

type family Nest (t::AT) (a::AT) :: AT where
    Nest 'Id     t       = t
    Nest t       'Id     = t
    Nest 'Scalar (Tag 'Scalar t) = Tag 'Scalar t
    Nest s       (Tag 'Id     t) = Tag s       t
    Nest s       t       = Tag s t
