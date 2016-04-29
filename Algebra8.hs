{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Algebra8
    where

import LocalPrelude
-- import Prelude (Functor(..), Applicative(..), Monad(..))
import Prelude ((.))
import qualified Prelude as P

import Unsafe.Coerce

import Data.Kind
import GHC.TypeLits

--------------------------------------------------------------------------------

{-
class Category cat where
    type Ob cat a :: Constraint
    type Ob cat a = ()
    id :: Ob cat a => cat a a
    (.) :: cat b c -> cat a b -> cat a c

type Functor = Functor_ (->) (->)

class (Category cat1, Category cat2) => Functor_ cat1 cat2 f where
    fmap :: cat1 a b -> cat2 (f a) (f b)

----------------------------------------

data TagT (t::AT) cat a b = TagT (App t a -> App t b) (cat a b)

instance Category cat => Category (TagT t cat) where
    type Ob (TagT t cat) a = Ob cat a
    id = TagT id id
    (.) (TagT f1 g1) (TagT f2 g2) = TagT (f1.f2) (g1.g2)

class Category cat => TagCat t cat where
    unTag :: proxy t -> cat a b -> App t a -> App t b

instance Category cat => TagCat t (TagT t cat) where
    unTag _ (TagT f g) = f

instance {-#OVERLAPS#-} (Category cat, TagCat s cat) => TagCat s (TagT t cat) where
    unTag p (TagT f g) = unTag p g

($$) :: TagCat 'Id cat => cat a b -> a -> b
($$) f a = unTag (Proxy::Proxy 'Id) f a

--------------------

type family TagCats (ts::AT) :: Type -> Type -> Type where
    TagCats 'Id       = Hask
    TagCats (Tag s t) = TagT s (TagCats t)

----------------------------------------

type Hask = (->)

instance Category (->) where
    id = P.id
    (.) = (P..)

instance TagCat 'Id (->) where
    unTag _ f = f
-}

--------------------------------------------------------------------------------

type family Logic  a
type family Scalar a

class Poset a where
    inf :: a -> a -> a

(&&) :: Poset a => a -> a -> a
(&&) = inf

-- class Topology a where
class Poset (Logic a) => Topology a where
--     type family Logic a
    (==) :: a -> a -> Logic a

class Topology a => Semigroup a where
    (+) :: a -> a -> a

-- class (Scalar (Scalar a)~Scalar a, Semigroup a) => Module a where
-- class (Scalar (Scalar a)~Scalar a, Semigroup (Scalar a), Semigroup a) => Module a where
class (Scalar (Scalar a)~Scalar a, Module (Scalar a), Semigroup a) => Module a where
--     type family Scalar a
-- class Semigroup a => Module a where
-- class (Semigroup a, Semigroup (Scalar a)) => Module a where
-- class (Semigroup a, Module (Scalar a)) => Module a where
    (.*) :: Scalar a -> a -> a

class Module a => Hilbert a where
    (<>) :: a -> a -> Scalar a


----------------------------------------

type instance Logic Bool = Bool
type instance Scalar Bool = ()
instance Poset Bool where
    inf = (P.&&)
instance Topology Bool where
--     type Logic Bool = Bool
    (==) = (P.==)

type instance Logic Int = Bool
type instance Scalar Int = Int
instance Poset Int where
    inf = P.min
instance Topology Int where
--     type Logic Int = Int
    (==) = (P.==)
instance Semigroup Int where (+) = (P.+)
instance Module Int where
--     type Scalar Int = Int
    (.*) = (P.*)
instance Hilbert Int where
    (<>) = (P.*)

type instance Logic (a,b) = (Logic a, Logic b)
type instance Scalar (a,b) = Scalar b
instance (Poset a, Poset b) => Poset (a,b) where
    inf (a1,b1) (a2,b2) = (inf a1 a2, inf b1 b2)
instance (Topology a, Topology b) => Topology (a,b) where
--     type Logic (a,b) = (Logic a, Logic b)
    (a1,b1)==(a2,b2) = (a1==a2,b1==b2)
instance (Semigroup a, Semigroup b) => Semigroup (a,b) where
    (a1,b1)+(a2,b2) = (a1+a2,b1+b2)
instance (Module a, Module b, Semigroup (Scalar b), Scalar a~Scalar b) => Module (a,b) where
--     type Scalar (a,b) = Scalar b
    s.*(a,b) = (s.*a,s.*b)
instance (Hilbert a, Hilbert b, Semigroup (Scalar b), Scalar a~Scalar b) => Hilbert (a,b) where
    (a1,b1)<>(a2,b2) = (a1<>a2)+(b1<>b2)

--------------------------------------------------------------------------------

type Space = Hilbert

x :: Expr Space (Int,Int)
x = Pure (1,5)

y :: Expr Space (Int,Int)
y = Pure (1,4)

z :: Scalar (ExprType (Int,Int) )
z = Pure 3

--------------------------------------------------------------------------------

type Expr alg a = Free (Sig alg) '[] a

type ExprAlg  alg = Free (Sig alg      ) '[] Var
type ExprType a   = Free (Sig Universal) '[] a

data Free (f::[AT]->Type->Type) (t::[AT]) (a::Type) where
    FreeTag  :: TypeConstraints t a => f (s ': t) (Free f t a)  -> Free f (s ': t) a
    Free     :: TypeConstraints t a => f       t  (Free f t a)  -> Free f       t  a
    Pure     :: App t a -> Free f t a

--------------------

instance
    ( Show      (App t a)
    , Show      (f t (Free f t a))
    , ShowUntag (f t (Free f t a))
    ) => Show (Free f t a)
        where
    show (FreeTag     f) = "("++show f++")"
    show (Free        f) = "("++show f++")"
    show (Pure        a) = show a

type family ShowUntag (f::Type) :: Constraint where
    ShowUntag (f (s ':  t) (Free f (s ':  t) a))  = Show (f (s ':  t) (Free f          t  a))
    ShowUntag a = ()

-- NOTE:
-- Earlier versions of GHC can't use the ShowUntag family above,
-- and so they need the overlapping instances implementation below.
-- AFAIK, there is no disadvantage to this version.

-- instance
--     ( Show      (App t a)
--     , Show      (f t (Free f t a))
--     ) => Show (Free f t a)
--         where
--     show (Free        f) = show f
--     show (Pure        a) = show a
--
-- instance {-#OVERLAPS#-}
--     ( Show      (App (Tag s t) a)
--     , Show      (f (Tag s t) (Free f (Tag s t) a))
--     , Show      (f (Tag s t) (Free f (      t) a))
--     ) => Show (Free f (Tag s t) a)
--         where
--     show (FreeTag     f) = show f
--     show (Free        f) = show f
--     show (Pure        a) = show a

----------------------------------------

-- class Eval alg (t::AT) a where
--     go :: Free (Sig alg) t a -> App t a
--
-- instance
--     ( Functor (Sig alg 'Id)
--     , FAlgebra alg
--     , alg a
--     ) => Eval alg 'Id a
--         where
--     go (Free f) = alg (Proxy :: Proxy a)   $ fmap go f
--     go (Pure a) = a
--
-- instance
--     ( FAlgebra alg
--     , Functor (Sig alg (Tag s t))
--     , Eval alg t a
--     , alg a
--     ) => Eval alg (Tag s t) a
--         where
--     go (FreeTag     f) = algTag (Proxy :: Proxy a) $ fmap go f
--     go (Free        f) = alg    (Proxy :: Proxy a) $ fmap go f
--     go (Pure        a) = a

eval :: forall alg t a.
    ( FAlgebra alg
    , alg a
    ) => Free (Sig alg) t a -> App t a
eval (Pure    a) = a
eval (Free    s) = alg    (Proxy::Proxy a) $ mape eval s
eval (FreeTag s) = algTag (Proxy::Proxy a) $ mape eval s

----------------------------------------

type instance Logic  (Free (Sig alg) t a) = Free (Sig alg) ('Logic  ': t) a
-- type instance Scalar (Free (Sig alg) t a) = Free (Sig alg) ('Scalar ': t) a
type instance Scalar (Free (Sig alg) t a) = Free (Sig alg) (AppScalar t) a

type family AppScalar (xs::[AT]) :: [AT] where
    AppScalar ('Scalar ': xs) = 'Scalar ': xs
    AppScalar xs              = 'Scalar ': xs

type TypeConstraints (t::[AT]) (a::Type)
    = (App (AppScalar t) a ~ Scalar (App t a))

----------------------------------------

class FAlgebra (alg::Type->Constraint) where
    data Sig alg (t::[AT]) a

    algTag :: alg a => proxy a -> Sig alg (s ':  t) (App t a) -> App (s ':  t) a
    alg    :: alg a => proxy a -> Sig alg        t  (App t a) -> App        t  a

    mape :: (TypeConstraints t' a)
         => (forall s. Free (Sig alg') s a -> App s a)
         -> Sig alg t (Free (Sig alg') t' a)
         -> Sig alg t (App t' a)

--------------------

class FAlgebra alg => Variety alg where
    laws :: [Law alg]

newtype Var = Var String

instance Show Var where
    show (Var x) = x

var1 :: Free (Sig f) '[] Var
var1 = Pure $ Var "var1"

var2 :: Free (Sig f) '[] Var
var2 = Pure $ Var "var2"

var3 :: Free (Sig f) '[] Var
var3 = Pure $ Var "var3"

data Law (alg::Type->Constraint) = forall t. Law
    { lawName :: String
    , lhs :: Free (Sig alg) '[] Var
    , rhs :: Free (Sig alg) '[] Var
    }

instance Show (Free (Sig alg) '[] Var) => Show (Law alg) where
    show (Law lawName lhs rhs) = show lhs ++ " = " ++ show rhs

--------------------------------------------------------------------------------

-- class Functor f where
--     type Elem f :: Type
--     type SetElem f a :: Type
-- --     fmap :: (Elem f -> b) -> f -> SetElem f b
--     fmap :: (a -> Elem f) -> SetElem f a -> f
--
-- instance Functor [a] where
--     type Elem [a] = a
--     type SetElem [a] b = [b]
--     fmap = P.map
--
-- instance FAlgebra Functor where
--     data Sig Functor t f where
-- --         Sfmap :: (Elem f -> b) -> f -> Sig Functor '[] f
--         Sfmap :: (a -> Elem f) -> SetElem f a -> Sig Functor '[] f
--
--     alg p (Sfmap e1 e2) = fmap e1 e2
--
--     algTag = error "Functor.algTag"
--
--     mape f (Sfmap e1 e2) = undefined -- Sfmap (_ e1) (_ e2)
--
-- instance Show (Sig Functor t f) where
--     show (Sfmap e1 e2) = "fmap <<function>> " -- ++show e2

--------------------------------------------------------------------------------

class Universal x
instance Universal x

class Subclass (cxt1::Type->Constraint) (cxt2::Type->Constraint) (t::[AT]) where
    proveAlg :: Proxy cxt1
             -> Proxy cxt2
             -> Proxy t
             -> (alg        a  => proxy a -> Sig alg t (App t a) -> App t a)
             -> (alg (App t a) => proxy a -> Sig alg t (App t a) -> App t a)

    proveAlgTag :: (t ~ (s ': s'))
                => Proxy cxt1
                -> Proxy cxt2
                -> Proxy t
                -> (alg         a  => proxy a -> Sig alg (s ': s') (App s' a) -> App (s ': s') a)
                -> (alg (App s' a) => proxy a -> Sig alg (s ': s') (App s' a) -> App (s ': s') a)

    proveU :: ()
           => Proxy cxt1
           -> Proxy cxt2
           -> Proxy t
           -> (( alg a
               , Show (Sig alg t a)
               ) => Proxy alg' -> Proxy alg -> Proxy t -> Sig alg t a -> Sig Universal t a)
           -> (( --alg (App t a)
               ) => Proxy alg' -> Proxy alg -> Proxy t -> Sig alg t a -> Sig Universal t a)


instance Subclass Poset Poset '[] where
    proveAlg    _ _ _ = P.id
--     proveU      _ _ _ = P.id

instance FAlgebra Universal where
    data Sig Universal t a where
        U :: forall alg' alg t a.
            ( FAlgebra alg
            , Show (Sig alg t a)
            , alg a
            , Subclass alg' alg t
            ) => Proxy alg'
              -> Proxy alg
              -> Proxy t
              -> Sig alg t a
              -> Sig Universal t a


    alg    p (U p1 p2 pt a) = proveAlg    p1 p2 pt alg    p a
    algTag p (U p1 p2 pt a) = proveAlgTag p1 p2 pt algTag p a

    mape f (U p1 p2 pt a) = proveU p1 p2 pt U p1 p2 pt (mape f a)

instance Show (Sig Universal t a) where
    show (U _ _ _ a) = show a

instance (Show a, Poset a) => Poset (Free (Sig Universal) '[] a) where
    inf e1 e2 = Free $ U (Proxy::Proxy Poset) (Proxy::Proxy Poset) (Proxy::Proxy '[]) $ Si e1 e2

toUniversal :: Free (Sig alg) '[] a -> Free (Sig Universal) '[] a
toUniversal (Pure a) = (Pure a)

--------------------------------------------------------------------------------

instance FAlgebra Poset where
    data Sig Poset t a where
        Si :: a -> a -> Sig Poset '[] a
    alg    _ (Si a1 a2) = inf a1 a2
    algTag _ _          = error "Poset.algTag should not be constructible"

    mape f (Si e1 e2) = Si (f e1) (f e2)

instance Variety Poset where
    laws =
        [ Law
            { lawName = "associative"
            , lhs = (var1&&var2)&&var3
            , rhs = var1&&(var2&&var3)
            }
        , Law
            { lawName = "commutative"
            , lhs = var1&&var2
            , rhs = var2&&var1
            }
        ]

instance Show a => Show (Sig Poset t a) where
    show (Si a1 a2) = show a1++"&&"++show a2

instance Poset (Free (Sig Poset) '[] a) where
    inf e1 e2 = Free $ Si e1 e2

----------------------------------------

instance FAlgebra Topology where
    data Sig Topology t a where
        ST :: {-#UNPACK#-}!(Sig Poset '[] (Logic a)) -> Sig Topology '[ 'Logic] a
        Se :: a -> a -> Sig Topology '[ 'Logic] a

    alg _ _ = error "Topology.alg should not be constructible"
    algTag p (ST s)     = alg Proxy s
    algTag p (Se a1 a2) = a1==a2

    mape f (ST s) = ST $ mape f s
    mape f (Se e1 e2) = Se (f e1) (f e2)

instance (Show (Logic a), Show a) => Show (Sig Topology t a) where
    show (ST a) = show a
    show (Se a1 a2) = show a1++"=="++show a2

instance {-#OVERLAPS#-}
    Show (Sig Topology ['Logic,'Logic] a) where
    show _ = "<<overflow>>"

instance Poset (Free (Sig Topology) '[ 'Logic] a) where
    inf e1 e2 = FreeTag $ ST $ Si e1 e2

instance Topology (Free (Sig Topology) '[] a) where
--     type Logic (Free (Sig Topology) 'Id a) = Free (Sig Topology) (Tag 'Logic 'Id) a
    (==) e1 e2 = FreeTag $ Se e1 e2

----------------------------------------

instance FAlgebra Semigroup where
    data Sig Semigroup t a where
        SS :: {-#UNPACK#-}!(Sig Topology t a) -> Sig Semigroup t a
        Sa :: a -> a -> Sig Semigroup '[] a

    algTag p (SS s)     = algTag p s
    alg    p (SS s)     = alg    p s
    alg    p (Sa a1 a2) = a1+a2

    mape f (SS s) = SS $ mape f s
    mape f (Sa e1 e2) = Sa (f e1) (f e2)

instance (Show (Logic a), Show a) => Show (Sig Semigroup t a) where
    show (SS s) = show s
    show (Sa a1 a2) = show a1++"+"++show a2

instance {-#OVERLAPS#-}
    Show (Sig Semigroup '[ 'Logic, 'Logic ] a) where
    show _ = "<<overflow>>"

instance Poset (Free (Sig Semigroup) '[ 'Logic ] a) where
    inf e1 e2 = FreeTag $ SS $ ST $ Si e1 e2

instance Topology (Free (Sig Semigroup) '[] a) where
    (==) e1 e2 = FreeTag $ SS $ Se e1 e2

instance Semigroup (Free (Sig Semigroup) '[] a) where
    (+) e1 e2 = Free $ Sa e1 e2

----------------------------------------

instance FAlgebra Module where
    data Sig Module t a where
        SM  :: {-#UNPACK#-}!(Sig Semigroup t          a) -> Sig Module t                   a
        SN1 :: {-#UNPACK#-}!(Sig Semigroup '[ 'Logic] a) -> Sig Module '[ 'Logic,'Scalar ] a
        SN2 :: {-#UNPACK#-}!(Sig Module    '[       ] a) -> Sig Module '[        'Scalar ] a
        Sp :: Scalar a -> a -> Sig Module '[] a

    alg    p            (SM s)     = alg p                         s
    alg    (p::proxy a) (SN1 s)    = alg (Proxy::Proxy (Scalar a)) s
    alg    (p::proxy a) (SN2 s)    = alg (Proxy::Proxy (Scalar a)) s
    alg    p            (Sp a1 a2) = a1.*a2

    algTag p            (SM  s) = algTag p s
    algTag (p::proxy a) (SN1 s) = algTag (Proxy::Proxy (Scalar a)) s
--     algTag (p::proxy a) (SN2 s) = algTag (Proxy::Proxy (       a)) s

    mape f (SM  s) = SM  $ mape f s
    mape f (SN1 s) = SN1 $ mape f s
    mape f (SN2 s) = SN2 $ mape f s
    mape f (Sp a1 a2) = Sp (f a1) (f a2)

instance
    ( Show a
    , Show (Logic a)
    , Show (Scalar a)
    ) => Show (Sig Module t a)
        where
    show (SM s) = show s
    show (SN1 s) = show s
    show (SN2 s) = show s
    show (Sp a1 a2) = show a1++".*"++show a2

instance {-#OVERLAPS#-} Show (Sig Module '[ 'Scalar, t ] a) where show _ = "<<overflow>>"
instance {-#OVERLAPS#-} Show (Sig Module '[ 'Logic , t ] a) where show _ = "<<overflow>>"

instance Poset (Free (Sig Module) '[ 'Logic ] a) where
    inf e1 e2 = FreeTag $ SM $ SS $ ST $ Si e1 e2

instance Topology (Free (Sig Module) '[] a) where
     (==) e1 e2 = FreeTag $ SM $ SS $ Se e1 e2

instance Semigroup (Free (Sig Module) '[] a) where
    (+) e1 e2 = Free $ SM $ Sa e1 e2

instance Scalar (Scalar a) ~ Scalar a => Module (Free (Sig Module) '[] a) where
    (.*) e1 e2 = Free $ Sp e1 e2

instance Scalar (Scalar a) ~ Scalar a => Poset (Free (Sig Module) '[ 'Logic, 'Scalar ] a) where
    inf e1 e2 = FreeTag $ SN1 $ SS $ ST $ Si e1 e2

instance Scalar (Scalar a) ~ Scalar a => Topology (Free (Sig Module) '[ 'Scalar ] a) where
    (==) e1 e2 = FreeTag $ SN1 $ SS $ Se e1 e2

instance Scalar (Scalar a) ~ Scalar a => Semigroup (Free (Sig Module) '[ 'Scalar ] a) where
    (+) e1 e2 = Free    $ SN2 $ SM $ Sa e1 e2

instance Scalar (Scalar a) ~ Scalar a => Module (Free (Sig Module) '[ 'Scalar ] a) where
    (.*) e1 e2 = Free $ SN2 $ Sp e1 e2

----------------------------------------

instance FAlgebra Hilbert where
    data Sig Hilbert t a where
        SH :: {-#UNPACK#-}!(Sig Module t a) -> Sig Hilbert t a
        Sd :: a -> a -> Sig Hilbert '[ 'Scalar ] a

    alg    p (SH s) = alg    p s
    algTag p (SH s) = algTag p s
    algTag p (Sd a1 a2) = a1<>a2

    mape f (SH s) = SH $ mape f s
    mape f (Sd a1 a2) = Sd (f a1) (f a2)

instance
    ( Show a
    , Show (Logic a)
    , Show (Scalar a)
    ) => Show (Sig Hilbert t a)
        where
    show (SH s) = show s
    show (Sd a1 a2) = show a1++"<>"++show a2

instance {-#OVERLAPS#-} Show (Sig Hilbert '[ 'Scalar, t ] a) where show _ = "<<overflow>>"
instance {-#OVERLAPS#-} Show (Sig Hilbert '[ 'Logic , t ] a) where show _ = "<<overflow>>"

instance Poset (Free (Sig Hilbert) '[ 'Logic ] a) where
    inf e1 e2 = FreeTag $ SH $ SM $ SS $ ST $ Si e1 e2

instance Topology (Free (Sig Hilbert) '[] a) where
    (==) e1 e2 = FreeTag $ SH $ SM $ SS $ Se e1 e2

instance Semigroup (Free (Sig Hilbert) '[] a) where
    (+) e1 e2 = Free $ SH $ SM $ Sa e1 e2

instance Scalar (Scalar a) ~ Scalar a => Module (Free (Sig Hilbert) '[] a) where
    (.*) e1 e2 = Free $ SH $ Sp e1 e2

instance Scalar (Scalar a) ~ Scalar a => Hilbert (Free (Sig Hilbert) '[] a) where
    (<>) e1 e2 = FreeTag $ Sd e1 e2

instance Scalar (Scalar a) ~ Scalar a => Poset (Free (Sig Hilbert) '[ 'Logic, 'Scalar ] a) where
    inf e1 e2 = FreeTag $ SH $ SN1 $ SS $ ST $ Si e1 e2

instance Scalar (Scalar a) ~ Scalar a => Topology (Free (Sig Hilbert) '[ 'Scalar ] a) where
    (==) e1 e2 = FreeTag $ SH $ SN1 $ SS $ Se e1 e2

instance Scalar (Scalar a) ~ Scalar a => Semigroup (Free (Sig Hilbert) '[ 'Scalar ] a) where
    (+) e1 e2 = Free    $ SH $ SN2 $ SM $ Sa e1 e2

instance Scalar (Scalar a) ~ Scalar a => Module (Free (Sig Hilbert) '[ 'Scalar ] a) where
    (.*) e1 e2 = Free    $ SH $ SN2 $ SM $ Sa e1 e2

--------------------------------------------------------------------------------

data AT
    = Scalar
    | Logic

type family App (t::k) (a::Type) ::  Type
type instance App '[]           a = a
type instance App ((x::AT)':xs) a = App x (App xs a)
type instance App 'Scalar a = Scalar a
type instance App 'Logic  a = Logic  a

type family Snoc (xs :: [k]) (y::k) where
    Snoc '[]       y = '[y]
    Snoc (x ': xs) y = x ': (Snoc xs y)

type family (++) (xs1:: [x]) (xs2:: [x]) :: [x] where
    '[] ++ '[] = '[]
    '[] ++ xs2 = xs2
    xs1 ++ '[] = xs1
    (x ': xs1) ++ xs2 = x ': (xs1++xs2)


-- type instance App (Tag t t') a = App t (App t' a)

-- type family MaybeTag (s::[AT]) (t::[AT]) where
--     MaybeTag 'Scalar (Tag 'Scalar t) = (Tag 'Scalar t)
--     MaybeTag s t = Tag s t

-- type family Nest (t::AT) (a::AT) :: AT where
--     Nest 'Id     t       = t
--     Nest t       'Id     = t
--     Nest 'Scalar (Tag 'Scalar t) = Tag 'Scalar t
--     Nest s       (Tag 'Id     t) = Tag s       t
--     Nest s       t       = Tag s t
