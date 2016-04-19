{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeFamilyDependencies #-}
-- {-# LANGUAGE AllowAmbiguousTypes #-}
module Algebra7
    where

import LocalPrelude
import Prelude (Functor(..), Applicative(..), Monad(..))
import qualified Prelude as P

import Unsafe.Coerce

import GHC.TypeLits

--------------------------------------------------------------------------------

class Poset a where
    inf :: a -> a -> a

(&&) :: Poset a => a -> a -> a
(&&) = inf

-- class Topology a where
class Poset (Logic a) => Topology a where
    type Logic a
    (==) :: a -> a -> Logic a

class Topology a => Semigroup a where
    (+) :: a -> a -> a

-- class (Scalar (Scalar a)~Scalar a, Semigroup a) => Module a where
-- class Semigroup a => Module a where
class (Semigroup a, Module (Scalar a)) => Module a where
    type family Scalar a
    (.*) :: Scalar a -> a -> a

class Module a => Hilbert a where
    (<>) :: a -> a -> Scalar a


----------------------------------------

instance Poset Bool where
    inf = (P.&&)
instance Topology Bool where
    type Logic Bool = Bool
    (==) = (P.==)

instance Topology Int where
    type Logic Int = Bool
    (==) = (P.==)
instance Semigroup Int where (+) = (P.+)
instance Module Int where
    (.*) = (P.*)
    type Scalar Int = Int
instance Hilbert Int where
    (<>) = (P.*)

instance (Poset a, Poset b) => Poset (a,b) where
    inf (a1,b1) (a2,b2) = (inf a1 a2, inf b1 b2)
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
-- type Space = Module

x :: Expr Space 'Id (Int,Int)
x = Pure (2,2)

y :: Expr Space 'Id (Int,Int)
y = Pure (1,3)

z :: Scalar (Expr Space 'Id (Int,Int))
z = Pure 2

--------------------------------------------------------------------------------

data Free (f::AT->Type->Type) (t::AT) (a::Type) where
    FreeTag  :: Proxy s -> Proxy t -> f (     Tag s t  ) (Free f t a)  -> Free f (     Tag s t  ) a
    Free     ::                       f             t    (Free f t a)  -> Free f             t    a
    Pure     :: App t a -> Free f t a

--------------------

instance
    ( Show      (App t a)
    , Show      (f t (Free f t a))
    , ShowUntag (f t (Free f t a))
    ) => Show (Free f t a)
        where
    show (FreeTag _ _ f) = show f
    show (Free        f) = show f
    show (Pure        a) = show a

--------------------

type family ShowUntag (f::Type) :: Constraint where
    ShowUntag (f (Tag s   t) (Free f (Tag s   t) a))  = Show (f (Tag s   t) (Free f          t  a))
    ShowUntag _ = ()

--------------------

class Taggable (s::AT) (t::AT) where
    freeTag  :: Proxy s -> Proxy t -> f (MaybeTag s t  ) (Free f t a)  -> Free f (MaybeTag s t  ) a

instance {-#OVERLAPS#-} Taggable 'Scalar (Tag 'Scalar t) where
    freeTag _ _ = Free

instance {-#OVERLAPS#-} MaybeTag s t ~ Tag s t => Taggable s t where
    freeTag p1 p2 = FreeTag p1 p2

--------------------

instance Functor (f t) => Functor (Free f t) where
    fmap g (Free f) = Free (fmap (fmap g) f)
--     fmap g (Pure a) = Pure $ g a


----------------------------------------

type Expr alg t a = Free (Sig alg) t a

class Eval alg (t::AT) a where
    go :: Expr alg t a -> App t a

instance
    ( Functor (Sig alg 'Id)
    , FAlgebra alg
    , alg a
    ) => Eval alg 'Id a
        where
    go (Free f) = algFree (Proxy::Proxy a) $ fmap go f
    go (Pure a) = a

instance
    ( FAlgebra alg
    , Functor (Sig alg (Tag s t))
--     , alg (App (Tag s t) a)
--     , alg (App (      t) a)
    , Eval alg t a
    , alg a
    ) => Eval alg (Tag s t) a
        where
--     go (FreeTag _ _ f) = _algFreeTag (Proxy::Proxy a) $ fmap go f
--     go (Free        f) = algFree    (Proxy::Proxy a) $ fmap go f
    go (FreeTag _ _ f) = algTag     (Proxy::Proxy a) $ fmap go f
    go (Free        f) = alg        (Proxy::Proxy a) $ fmap go f
    go (Pure        a) = a

--------------------

-- class Reduce alg t a where
--     reduce :: Expr alg t a -> Expr alg 'Id (App t a)
--
-- instance Reduce alg 'Id a where
--     reduce (Free f) = Free f
--     reduce (Pure a) = Pure a
--
-- instance
--     ( Functor (Sig alg (Tag s t))
--     ) => Reduce alg (Tag s t) a where
--     reduce (Free        f) = Free $ unTag $ fmap reduce f
--     reduce (Pure        a) = Pure a
--
-- unTag :: Sig alg t a -> Sig alg 'Id a
-- unTag = unsafeCoerce

--------------------------------------------------------------------------------

class FAlgebra (alg::Type->Constraint) where
    data Sig alg (t::AT) a
    algFreeTag :: alg (App t a) => proxy a -> Sig alg (Tag s t) (App t a) -> App (Tag s t) a
    algFree    :: alg (App t a) => proxy a -> Sig alg        t  (App t a) -> App        t  a

--     algFreeTag :: Ancestor alg (Tag s t) a => proxy a -> Sig alg (Tag s t) (App t a) -> App (Tag s t) a
--     algFreeTag :: Ancestor alg (      t) a => proxy a -> Sig alg (Tag s t) (App t a) -> App (Tag s t) a
--     algFree    :: Ancestor alg t a         => proxy a -> Sig alg        t  (App t a) -> App        t  a

    algTag :: alg a => proxy a -> Sig alg (Tag s t) (App t a) -> App (Tag s t) a
    alg    :: alg a => proxy a -> Sig alg        t  (App t a) -> App        t  a

    alg'  :: alg a => proxy a -> Sig alg 'Id a -> a
    alg'' :: alg a => proxy a -> Sig alg (Tag s t) a -> App (    s  ) a

----------------------------------------

instance FAlgebra Poset where
    data Sig Poset t a where
        Pi :: a -> a -> Sig Poset t a
        Pj :: a -> a -> Sig Poset 'Id a

    algFreeTag p _          = error "Poset.algFreeTag should never be called"
    algFree    p (Pi e1 e2) = inf e1 e2

    alg _ (Pj e1 e2) = inf e1 e2
--     alg _ (Pi e1 e2) = inf e1 e2

instance Show a => Show (Sig Poset t a) where
    show (Pi a1 a2) = "("++show a1++"&&"++show a2++")"

instance Functor (Sig Poset t) where
    fmap f (Pi a1 a2) = Pi (f a1) (f a2)

instance Poset (Expr Poset 'Id a) where
    inf e1 e2 = Free (Pi e1 e2)

----------------------------------------

instance FAlgebra Topology where
    data Sig Topology t a where
        ST :: {-#UNPACK#-}!(Sig Poset (Tag 'Logic t) a) -> Sig Topology (Tag 'Logic t) a
        Se :: a -> a -> Sig Topology (MaybeTag 'Logic t) a

--     algFreeTag p (ST s)     = algFreeTag p s
    algFreeTag p (Se a1 a2) = a1==a2
--     algFree    p (ST s)     = algFree p s

instance Show a => Show (Sig Topology t a) where
    show (ST a)     = show a
    show (Se a1 a2) = "("++show a1++"=="++show a2++")"

instance Functor (Sig Topology t) where
    fmap f (Se a1 a2) = Se (f a1) (f a2)

instance Poset (Expr Topology (Tag 'Logic t) a) where
--     inf e1 e2 = Free $ ST $ Pi e1 e2
--     inf e1 e2 = Free $ SU $ Pi e1 e2

instance Poset (Expr Topology (Tag 'Logic 'Id) a) where
    inf e1 e2 = Free $ ST $ Pi e1 e2

instance Topology (Expr Topology t a) where
    type Logic (Expr Topology t a) = Expr Topology (MaybeTag 'Logic t) a
    (==) e1 e2 = FreeTag (Proxy::Proxy 'Logic) (Proxy::Proxy t) $ Se e1 e2

----------------------------------------

instance FAlgebra Semigroup where
    data Sig Semigroup t a where
        SS :: {-#UNPACK#-}!(Sig Topology t a) -> Sig Semigroup t a
        Sp :: a -> a -> Sig Semigroup t a

    algFreeTag p (SS s)     = algFreeTag p s
    algFree    p (SS s)     = algFree p s
    algFree    p (Sp a1 a2) = a1+a2

instance Show a => Show (Sig Semigroup t a) where
    show (SS s) = show s
    show (Sp a1 a2) = "("++show a1++"+"++show a2++")"

instance Functor (Sig Semigroup t) where
    fmap f (SS s)     = SS $ fmap f s
    fmap f (Sp a1 a2) = Sp (f a1) (f a2)

instance Poset (Expr Semigroup (Tag 'Logic t) a) where
    inf e1 e2 = Free $ SS $ ST $ Pi e1 e2

instance Topology (Expr Semigroup t a) where
    type Logic (Expr Semigroup t a) = Expr Semigroup (MaybeTag 'Logic t) a
    (==) e1 e2 = FreeTag (Proxy::Proxy 'Logic) (Proxy::Proxy t) $ SS $ Se e1 e2

instance Semigroup (Expr Semigroup t a) where
    (+) e1 e2 = Free $ Sp e1 e2

----------------------------------------

instance FAlgebra Module where
    data Sig Module t a where
        SM :: {-#UNPACK#-}!(Sig Semigroup              t  a) -> Sig Module              t  a
        SN :: {-#UNPACK#-}!(Sig Module    (Tag 'Scalar t) a) -> Sig Module (Tag 'Scalar t) a
        Sm :: Scalar a -> a -> Sig Module t a

    algFreeTag p (SM m)   = algFreeTag p m
    algFreeTag p (SN n)   = algFreeTag p n
--     algFreeTag p (Sm s a) = s.*a
    algFree    p (SM m)   = algFree    p m
    algFree    p (SN n)   = algFree    p n
    algFree    p (Sm s a) = s.*a


instance
    ( Show a
    , Show (Scalar a)
    ) => Show (Sig Module t a)
        where
    show (SM m) = show m
    show (SN n) = show n
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

instance Functor (Sig Module t) where
    fmap f (SM s) = SM $ fmap f s
    fmap f (SN s) = SN $ fmap f s
    fmap f (Sm s a) = Sm (unsafeCoerce f s) (f a)

instance Poset (Expr Module (Tag 'Logic t) a) where
    inf e1 e2 = Free $ SM $ SS $ ST $ Pi e1 e2

instance Topology (Expr Module t a) where
    type Logic (Expr Module t a) = Expr Module (MaybeTag 'Logic t) a
    (==) e1 e2 = FreeTag (Proxy::Proxy 'Logic) (Proxy::Proxy t) $ SM $ SS $ Se e1 e2

instance Semigroup (Expr Module 'Id a) where
    (+) e1 e2 = Free $ SM $ Sp e1 e2

instance Semigroup (Expr Module (Tag 'Scalar 'Id) a) where
    (+) e1 e2 = Free $ SN $ SM $ Sp e1 e2

instance Module (Expr Module 'Id a) where
    type Scalar (Expr Module 'Id a) = Expr Module (MaybeTag 'Scalar 'Id) a
    (.*) e1 e2 = Free $ Sm e1 e2

instance Module (Expr Module (Tag 'Scalar 'Id) a) where
    type Scalar (Expr Module (Tag 'Scalar 'Id) a) = Expr Module (MaybeTag 'Scalar (Tag 'Scalar 'Id)) a
    (.*) e1 e2 = Free $ SN $ Sm e1 e2

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
        SH :: {-#UNPACK#-}!(Sig Module t a) -> Sig Hilbert t a
        Sd :: Proxy t
           -> a
           -> a
           -> Sig Hilbert (MaybeTag 'Scalar t) a

    algFreeTag p (SH m)       = algFreeTag p m
    algFreeTag p (Sd _ a1 a2) = unsafeCoerce $ a1<>a2
    algFree    p (SH m)       = algFree p m
--     algFree    p (Sd _ a1 a2) = a1<>a2

instance
    ( Show a
    , Show (Scalar a)
    ) => Show (Sig Hilbert t a)
        where
    show (SH h) = show h
    show (Sd _ a1 a2) = "("++show a1++"<>"++show a2++")"

-- NOTE:
-- I *believe* these overlapping instances are not required due to the class hierarchy collapsing the Scalar arguments.
-- There may still be class hierarchies that require overlapping instances?

instance {-#OVERLAPS#-}
    ( Show a
    ) => Show (Sig Hilbert (Tag 'Scalar (Tag 'Scalar t)) a)
        where
    show (SH h) = show h
    show (Sd _ a1 a2) = "("++show a1++"<>"++show a2++")"

instance {-#OVERLAPS#-}
    ( Show a
    ) => Show (Sig Hilbert (Tag 'Logic t) a)
        where
    show (SH h) = show h

instance Functor (Sig Hilbert t) where
    fmap f (SH h) = SH $ fmap f h
    fmap f (Sd p a1 a2) = Sd p (f a1) (f a2)

-- instance Poset (Expr Hilbert (Tag 'Logic t) a) where
--     inf e1 e2 = Free $ SH $ SM $ SS $ ST $ Pi e1 e2

instance Poset (Expr Hilbert (Tag 'Logic 'Id) a) where
    inf e1 e2 = Free $ SH $ SM $ SS $ ST $ Pi e1 e2

instance Poset (Expr Hilbert (Tag 'Logic (Tag 'Scalar 'Id)) a) where
    inf e1 e2 = Free $ SH $ SM $ SS $ ST $ Pi e1 e2

-- instance Topology (Expr Hilbert t a) where
--     type Logic (Expr Hilbert t a) = Expr Hilbert (MaybeTag 'Logic t) a
--     (==) e1 e2 = FreeTag (Proxy::Proxy 'Logic) (Proxy::Proxy t) $ SH $ SM $ SS $ Se e1 e2

instance Topology (Expr Hilbert 'Id a) where
    type Logic (Expr Hilbert 'Id a) = Expr Hilbert (MaybeTag 'Logic 'Id) a
    (==) e1 e2 = FreeTag (Proxy::Proxy 'Logic) (Proxy::Proxy t) $ SH $ SM $ SS $ Se e1 e2

instance Topology (Expr Hilbert (Tag 'Scalar 'Id) a) where
    type Logic (Expr Hilbert (Tag 'Scalar 'Id) a) = Expr Hilbert (MaybeTag 'Logic (Tag 'Scalar 'Id)) a
    (==) e1 e2 = FreeTag (Proxy::Proxy 'Logic) (Proxy::Proxy t) $ SH $ SM $ SS $ Se e1 e2

-- instance
-- --     ( Semigroup (App t a)
--     (
--     ) => Semigroup (Expr Hilbert 'Id a)
--         where
--     (+) e1 e2 = Free $ SH $ SM $ Sp e1 e2

instance Semigroup (Expr Hilbert 'Id a) where
    (+) e1 e2 = Free $ SH $ SM $ Sp e1 e2

instance Semigroup (Expr Hilbert (Tag 'Scalar 'Id) a) where
    (+) e1 e2 = Free $ SH $ SN $ SM $ Sp e1 e2

-- instance
-- --     ( Module (App t a)
-- --     , Module (App (MaybeTag 'Scalar t) a)
-- --     , MaybeTag 'Scalar (MaybeTag 'Scalar t) ~ MaybeTag 'Scalar t
--     (
--     ) => Module (Expr Hilbert 'Id a)
--         where
--     type Scalar (Expr Hilbert 'Id a) = Expr Hilbert (MaybeTag 'Scalar 'Id) a
--     (.*) e1 e2 = Free $ SH $ Sm e1 e2

instance Module (Expr Hilbert 'Id a) where
    type Scalar (Expr Hilbert 'Id a) = Expr Hilbert (MaybeTag 'Scalar 'Id) a
    (.*) e1 e2 = Free $ SH $ Sm e1 e2

instance Module (Expr Hilbert (Tag 'Scalar 'Id) a) where
    type Scalar (Expr Hilbert (Tag 'Scalar 'Id) a) = Expr Hilbert (MaybeTag 'Scalar (Tag 'Scalar 'Id)) a
    (.*) e1 e2 = Free $ SH $ SN $ Sm e1 e2

-- instance
-- --     ( Hilbert (App t a)
-- --     , Module (App (MaybeTag 'Scalar t) a)
-- --     , MaybeTag 'Scalar (MaybeTag 'Scalar t) ~ MaybeTag 'Scalar t
--     ( Taggable 'Scalar t
--     ) => Hilbert (Expr Hilbert t a)
--         where
--     (<>) e1 e2 = freeTag
--         (Proxy::Proxy 'Scalar)
--         (Proxy::Proxy t)
--         $ Sd (Proxy::Proxy t) e1 e2

instance Hilbert (Expr Hilbert 'Id a) where
    (<>) e1 e2 = FreeTag (Proxy::Proxy 'Scalar) (Proxy::Proxy 'Id) $ Sd (Proxy::Proxy 'Id) e1 e2

instance Hilbert (Expr Hilbert (Tag 'Scalar 'Id) a) where
    (<>) e1 e2 = Free                                              $ Sd (Proxy::Proxy (Tag 'Scalar 'Id)) e1 e2

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

-- type family MaybeTag (s::AT) (t::AT) = r | r -> s t where
type family MaybeTag (s::AT) (t::AT) where
    MaybeTag 'Scalar (Tag 'Scalar t) = (Tag 'Scalar t)
    MaybeTag s t = Tag s t

type family Nest (t::AT) (a::AT) :: AT where
    Nest 'Id     t       = t
    Nest t       'Id     = t
    Nest 'Scalar (Tag 'Scalar t) = Tag 'Scalar t
    Nest s       (Tag 'Id     t) = Tag s       t
    Nest s       t       = Tag s t
