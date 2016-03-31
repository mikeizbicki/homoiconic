{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveGeneric #-}

module Algebra
    where

import qualified Prelude as P
import LocalPrelude hiding ((.))
import Lattice
import Tests
import Topology1 hiding (Lawful (..), Semigroup (..), isLawful)
-- import Union
import Category

import Test.SmallCheck.Series hiding (NonNegative)
import Test.Tasty
import qualified Test.Tasty.SmallCheck as SC
import qualified Test.Tasty.QuickCheck as QC
import Test.QuickCheck hiding (Testable,NonNegative)

import Debug.Trace
import GHC.Generics

--------------------------------------------------------------------------------

type (><) a b = Prod a b
class (cxt1 a, cxt2 a) => Prod cxt1 cxt2 a
instance (cxt1 a, cxt2 a) => Prod cxt1 cxt2 a

class HetAlgebra (cxt :: Type -> Constraint) where
    type SuperClasses (cxt :: Type -> Constraint) :: Type -> Constraint
    type HetDomain cxt a :: *
    type HetRange cxt a :: *
    op :: cxt a => Proxy (cxt a) -> HetDomain cxt a -> HetRange cxt a

instance HetAlgebra Semigroup where
    type SuperClasses Semigroup = Topology
    type HetDomain Semigroup a = (a,a)
    type HetRange  Semigroup a = a
    op _ (a1,a2) = a1+a2

instance HetAlgebra Monoid where
    type SuperClasses Monoid = Semigroup >< Topology
    type HetDomain Monoid a = ()
    type HetRange  Monoid a = a
    op _ _ = zero

instance HetAlgebra Topology where
    type SuperClasses Topology = Topology
    type HetDomain Topology a = (a,a)
    type HetRange Topology a = Logic a
    op _ (a1,a2) = a1==a2

--------------------------------------------------------------------------------

data Mor (cxt::Type->Constraint) a b where
    Mor :: (cxt a, cxt b)
        => (HetDomain cxt a -> HetDomain cxt b)
        -> (HetRange  cxt a -> HetRange  cxt b)
        -> Mor cxt a b

class Invariant (a::Type) (name::Symbol) where
    type InvariantDomain name a :: Type
    type InvariantRange  name a :: Type
    invariant :: a -> InvariantDomain name a -> Logic (InvariantRange name a)

instance (HetAlgebra cxt, Topology (HetRange cxt b)) => Invariant (Mor cxt a b) "morphism" where
    type InvariantDomain "morphism" (Mor cxt a b) = HetDomain cxt a
    type InvariantRange  "morphism" (Mor cxt a b) = HetRange  cxt b
    invariant (Mor f g) a = g (op (Proxy::Proxy (cxt a))    a)
                         ==    op (Proxy::Proxy (cxt b)) (f a)

--------------------

data Box cxt where
    Box :: forall cxt a. cxt -> Box cxt

data Box2 (cxt :: Type -> Constraint) a b where
    Box2 :: forall cxt x a b. cxt (x a b) => x a b -> Box2 cxt a b

type (a+>b) cxt = Box2 cxt a b

-- ($$) :: forall a b cxt. (a+>b) cxt -> a -> b
-- ($$) (HomC f) = case (getMor f::Mor cxt a b) of Mor f g -> undefined

data (a->>b) cxt where
    HomC :: forall cxt cat a b. (Hom cxt cat, cxt a, cxt b) => cat a b -> (a->>b) cxt

($$) :: forall a b cxt. (a->>b) cxt -> a -> b
($$) (HomC f) = case (getMor f::Mor cxt a b) of Mor f g -> undefined

class Hom (cxt :: Type -> Constraint) (cat :: Type -> Type -> Type) where
    getMor :: (cxt a, cxt b) => cat a b -> Mor cxt a b

--------------------------------------------------------------------------------

data HomT (cxt :: Type -> Constraint) (cat :: Type -> Type -> Type) a b where
    HomT :: (cxt a, cxt b) => cat a b -> HomT cxt cat a b

instance Category cat => Category (HomT cxt cat) where
    type ValidObject (HomT cxt cat) a = (ValidObject cat a, cxt a)
    id = HomT id
    (HomT f1).(HomT f2) = HomT (f1.f2)

instance Concrete cat => Concrete (HomT cxt cat) where
    toHask (HomT f) = toHask f

-- instance Invariant (HomT Semigroup Hask a b) "morphism" where
--     type InvariantDomain "morphism" (HomT Semigroup Hask a b) = (a,a)
--     type InvariantRange  "morphism" (HomT Semigroup Hask a b) = (b,b)

--------------------------------------------------------------------------------

class Topology a => Semigroup a where
    infixr 6 +
    (+) :: a -> a -> a

instance Lawful Semigroup "associative" where
    type LawInput Semigroup "associative" a = (a,a,a)
    law _ _ _ (a1,a2,a3) = (a1+a2)+a3 == a1+(a2+a3)

--------------------

instance Semigroup Float where
    (+) = (P.+)

instance {-# OVERLAPS #-} Approximate Semigroup "associative" Float where
    maxError _ _ _ (a1,a2,a3) = Discrete $ NonNegative $ 2e-2

instance Semigroup Double where
    (+) = (P.+)

instance {-# OVERLAPS #-} Approximate Semigroup "associative" Double where
    maxError _ _ _ (a1,a2,a3) = Discrete $ NonNegative $ 2e-4

--------------------

instance (Semigroup a, Semigroup b) => Semigroup (a,b) where
    (a1,b1)+(a2,b2) = (a1+a2,b1+b2)

instance Semigroup () where
    ()+()=()

instance Semigroup Int where
    (+) = (P.+)

instance Semigroup Integer where
    (+) = (P.+)

instance Semigroup Rational where
    (+) = (P.+)

instance Topology a => Semigroup [a] where
    (+) = (P.++)

-- instance Semigroup a => Semigroup [a] where
--     (x:xr)+(y:yr) = x+y : xr+yr
--     []    +ys     = ys
--     xs    +[]     = xs

----------------------------------------

class Semigroup a => Monoid a where
    zero :: a

instance Lawful Monoid "idempotent_right" where
    type LawInput Monoid "idempotent_right" a = a
    law _ _ _ a = a+zero == a

instance Lawful Monoid "idempotent_left" where
    type LawInput Monoid "idempotent_left" a = a
    law _ _ _ a = zero+a == a

instance Monoid Int      where zero = 0
instance Monoid Integer  where zero = 0
instance Monoid Float    where zero = 0
instance Monoid Double   where zero = 0
instance Monoid Rational where zero = 0

----------------------------------------

class Monoid a => Group a where
    {-# MINIMAL negate | (-) #-}
    negate :: a -> a
    negate a = zero - a

    (-) :: a -> a -> a
    a1-a2 = a1 + negate a2

instance Lawful Group "negate" where
    type LawInput Group "negate" a = a
    law _ _ _ a = negate a == zero - a

instance Lawful Group "(-)" where
    type LawInput Group "(-)" a = (a,a)
    law _ _ _ (a1,a2) = a1-a2 == a1+negate a2

instance Lawful Group "cancellative" where
    type LawInput Group "cancellative" a = a
    law _ _ _ a = zero == a-a

instance Group Int          where negate = P.negate
instance Group Integer      where negate = P.negate
instance Group Float        where negate = P.negate
instance Group Double       where negate = P.negate
instance Group Rational     where negate = P.negate

----------------------------------------

class Group a => Ring a where
    one :: a
    (*) :: a -> a -> a

class Ring a => Field a where
    {-# MINIMAL reciprocal | (/) #-}
    reciprocal :: a -> a
    reciprocal a = one / a

    (/) :: a -> a -> a
    a1/a2 = a1 * reciprocal a2

-- type Hask = (->)
--
-- class Semigroup (cat :: * -> * -> *) a where
--     (+) :: cat a (cat a a)
--
-- instance Semigroup (->) Float where
--     (+) = (P.+)
--
-- instance Semigroup (->) b => Semigroup (->) (a -> b) where
--     (+) f1 f2 = \a -> f1 a + f2 a
--
-- instance Semigroup Top Float where
--     (+) = Top
--         { arrow = \a1 -> Top
--             { arrow = \a2 -> a1 P.+ a2
--             , inv = \_ nb -> nb
--             }
--         , inv = \a (_,nb) -> nb
--         }
--
-- instance (Semigroup (->) b, Semigroup Top b) => Semigroup (->) (Top a b) where
--     (+) (Top f1 inv1) (Top f2 inv2) = Top
--         { arrow = f1 + f2
--         , inv = undefined
--         }

class (Semigroup a, Semigroup (Scalar a)) => Module a where
    (.*) :: a -> Scalar a -> a

type instance Scalar (a,b) = Scalar b
instance (Module a, Module b, Scalar a~Scalar b) => Module (a,b) where
    (a,b).*s = (a.*s,b.*s)

class Module a => Hilbert a where
    (<>) :: a -> a -> Scalar a

instance (Hilbert a, Hilbert b, Scalar a~Scalar b) => Hilbert (a,b) where
    (a1,b1)<>(a2,b2) = a1<>a2 + b1<>b2

--------------------------------------------------------------------------------

data Free f e = Free (f (Free f e)) | Pure e

instance P.Functor f => P.Functor (Free f) where
    fmap g (Pure e) = Pure $ g e
    fmap g (Free f) = Free $ P.fmap (P.fmap g) f

-- instance Functor cat f => Functor cat (Free f) where
--     fmap g = _ $ Pure _ -- Pure $ toHask g e
--     fmap g (Free f) = Free $ P.fmap (P.fmap g) f

newtype Fix  f   = Fix  (f (Fix  f  ))
newtype Fix' f e = Fix' (f (Fix' f e))

instance P.Functor f => P.Functor (Fix' f) where
    fmap g (Fix' f) = Fix' $ P.fmap (P.fmap g) f

instance Functor Hask f => Functor Hask (Fix' f) where
    fmap' g (Fix' f) = Fix' $ fmap' (fmap' g) f

natFree' :: Functor cat f => (forall a. cat (f a) (g a)) -> Free f e -> Free g e
natFree' = undefined

natFree :: Functor Hask f => (forall a. f a -> g a) -> Free f e -> Free g e
natFree _ (Pure e) = Pure e
natFree x (Free f) = Free $ x $ fmap (natFree x) f

instance (Show e, Show (f (Free f e))) => Show (Free f e) where
    show (Pure e) = show e
    show (Free f) = show f

-- instance Metric (Free f e) where
-- type instance Scalar (Free f e) = Free f (Scalar e)
type instance Scalar Int = Int

--------------------

data Phylum
    = Id
    | Scalar
    | Logic
    | Elem
    | App Phylum Phylum

type family GetPhylum (p::Phylum) a
type instance GetPhylum Id a = a
type instance GetPhylum 'Scalar a = Scalar a
type instance GetPhylum 'Logic a = Logic a
-- type instance GetPhylum 'Elem a = Elem a
type instance GetPhylum (App p1 p2) a = GetPhylum p1 (GetPhylum p2 a)

type family CxtPhylum (f::Phylum) a where
    CxtPhylum (App p1 p2) a = GetPhylum p2 a
    CxtPhylum p a           = GetPhylum p  a

type instance Scalar (Expr cxt f a) = Scalar_ (Expr cxt f a)
type family Scalar_ a where
    Scalar_ (Expr cxt (App 'Scalar f) a) = (Expr cxt (App 'Scalar f) a)
    Scalar_ (Expr cxt              f  a) = (Expr cxt (App 'Scalar f) a)

type Expr cxt p a = Free (FExpr cxt p) a

instance Num a => Num (Expr cxt f a) where
    fromInteger n = Pure $ fromInteger n

--------------------

type family PsCatT (ps::[Phylum]) cat where
    PsCatT '[]    cat = cat
    PsCatT (p:ps) cat = PCatT p (PsCatT ps cat)

data PCatT (p::Phylum) cat a b = PCatT
    {-#UNPACK#-}!(cat a b)
    {-#UNPACK#-}!(GetPhylum p a -> GetPhylum p b)

instance Category cat => Category (PCatT p cat) where
    type ValidObject (PCatT p cat) a = ValidObject cat a
    id = PCatT id id
    (PCatT f1 g1).(PCatT f2 g2) = PCatT (f1.f2) (g1.g2)

class Category cat => PCat (p::Phylum) cat where
    getPhylumArrow :: proxy p -> cat a b -> GetPhylum p a -> GetPhylum p b

instance Category cat => PCat p (PCatT p cat) where
    getPhylumArrow _ (PCatT _ g) = g

instance (Category cat, PCat p' cat) => PCat p' (PCatT p cat) where
    getPhylumArrow p (PCatT f _) = getPhylumArrow p f

----------

class {-Functor cat (FExpr cxt) =>-} FAlgebra (cxt :: Type -> Constraint) where
    data FExpr cxt (p::Phylum) (a::Type)
    type FCxt  cxt (p::Phylum) (a::Type) :: Constraint
    runFExpr :: FCxt cxt p a => FExpr cxt p a -> GetPhylum p a

cataHask :: Functor Hask f => (f a -> a) -> Free f a -> a
cataHask g (Pure a) = a
cataHask g (Free f) = g $ fmap (cataHask g) f

cata :: (Concrete cat, Functor cat f) => cat (f a) a -> cat (Free f a) a
cata g = g . fmap (cata g) . unFix
    where
--         fmap :: cat a b -> cat (f a) (f b)
--         fmap = undefined

        unFix :: cat (Free f a) (f (Free f a))
        unFix = undefined

-- cata2 :: Functor cat f => cat (f a) a -> Free f a -> a
-- cata2 g (Pure a) = a
-- cata2 g (Free f) = g $ fmap (_ $ cata2 g) f

-- evalExpr :: (cxt~Semigroup, FAlgebra cxt) => Expr cxt p a -> GetPhylum p a
-- evalExpr (Free (FExpr_plus a1 a2)) = evalExpr a1 + evalExpr a2

-- cata g (Pure a) = a
-- cata g (Free f) = toHask g $ fmap (cata g) f

-- eval :: Expr cxt p a -> a
-- eval = _ . fmap eval . _

-- eval ::
--     ( Functor Hask (FExpr cxt p)
--     , FAlgebra cxt
--     , GetPhylum p (GetPhylum p a) ~ GetPhylum p a
--     , FCxt cxt p (GetPhylum p a)
--     ) => Expr cxt p a -> a
-- -- eval (Pure a) = a
-- eval (Free e) = runFExpr $ fmap eval e

--------------------

instance FAlgebra Semigroup where
    data FExpr Semigroup p a where
        FExpr_Semigroup
            :: {-#UNPACK#-}!(FExpr Topology p a)
            -> FExpr Semigroup p a
        FExpr_plus
            :: GetPhylum p a
            -> GetPhylum p a
            -> FExpr Semigroup p a
    type FCxt Semigroup p a = Semigroup (GetPhylum p a)
--     runFExpr (FExpr_Semigroup e) = runFExpr e
    runFExpr (FExpr_plus a1 a2) = a1+a2

instance Show (GetPhylum p a) => Show (FExpr Semigroup p a) where
    show (FExpr_plus a1 a2) = "("++show a1++"+"++show a2++")"

instance (cat~Hask, PCat p cat) => Functor cat (FExpr Semigroup p) where
    fmap f (FExpr_plus a1 a2) = FExpr_plus (getPhylumArrow p f a1) (getPhylumArrow p f a2)
        where
            p = (Proxy::Proxy p)

-- instance Category cat => Functor (PCatT p cat) (FExpr Semigroup p) where
--     fmap f = PCatT _f1 _f2 --undefined undefined -- FExpr_plus (getPhylumArrow p f a1) (getPhylumArrow p f a2)
--         where
--             f2 :: GetPhylum p (FExpr Semigroup p a) -> GetPhylum p (FExpr Semigroup p b)
-- --             f2 = undefined
-- --             f1 = undefined
--             f2 (FExpr_plus a1 a2) = undefined
-- --             f2  = undefined
-- --
-- --             p = (Proxy::Proxy p)

instance
    ( GetPhylum p (Expr Semigroup p a) ~ Expr Semigroup p a
    ) => Semigroup (Expr Semigroup p a)
        where
    e1+e2 = Free $ FExpr_plus e1 e2

--------------------

{-
instance FAlgebra Topology where
    data FExpr Topology p a where
        FExpr_eq
            :: GetPhylum p a
            -> GetPhylum p a
            -> FExpr Topology (App 'Logic p) a
    type FCxt Topology p a = FCxt_Topology p a
    runFExpr (FExpr_eq a1 a2) = a1==a2

type family FCxt_Topology p a where
    FCxt_Topology (App 'Logic p) a = Topology (GetPhylum p a)

instance Show (GetPhylum p a) => Show (FExpr Topology (App 'Logic p) a) where
    show (FExpr_eq a1 a2) = "("++show a1++"=="++show a2++")"

-}
-- FIXME:
-- This instance does NOT accomplish two important goals:
--  1. It can't be used to compare two Expr's to see how similar they are.
--  2. It can't be used to construct new Expr's with a simple syntax similar to how the Semigroup/etc instances can.
--  I don't know how to accomplish either of these goals.
instance Topology (Expr cxt p a) where
    type Neighborhood (Expr cxt p a) = ()
    (e1==e2) () = True

{-
--------------------

class Topology c => Container c where
    type Elem c
    elem :: Elem c -> c -> Logic c

instance Topology a => Container [a] where
    type Elem [a] = a
    elem = undefined

instance FAlgebra Container where
    data FExpr Container p a where
        FExpr_Container
            :: {-#UNPACK#-}!(FExpr Topology p a)
            -> FExpr Container p a
        FExpr_elem
            :: GetPhylum (App 'Elem p) a
            -> GetPhylum p a
            -> FExpr Container (App 'Logic p) a
    type FCxt Container p a = (FCxt_Container p a, FCxt_Topology p a)
    runFExpr (FExpr_Container e) = runFExpr e
    runFExpr (FExpr_elem ea a) = elem ea a

type family FCxt_Container p a where
    FCxt_Container (App 'Logic p) a = Container (GetPhylum p a)
    FCxt_Container p              a = FCxt_Topology p a

instance
    ( Show (GetPhylum p a)
    , Show (GetPhylum (App 'Elem p) a)
    ) => Show (FExpr Container (App 'Logic p) a)
        where
    show (FExpr_elem ea a) = "(elem "++show ea++" "++show a++")"

-- instance Container (Expr Container p a) where
--     elem ea a = FExpr_elem ea a

--------------------

--------------------

instance FAlgebra Module where
    data FExpr Module p a where
        FExpr_Module
            :: {-#UNPACK#-}!(FExpr Semigroup p a)
            -> FExpr Module p a
        FExpr_mul
            :: GetPhylum (App 'Scalar p) a
            -> GetPhylum p a
            -> FExpr Module p a
    type FCxt Module p a = Module (GetPhylum p a)
    runFExpr (FExpr_Module a) = runFExpr a
    runFExpr (FExpr_mul sa a) = a.*sa

instance
    ( Show (GetPhylum p a)
    , Show (GetPhylum (App 'Scalar p) a)
    ) => Show (FExpr Module p a)
        where
    show (FExpr_Module e) = show e
    show (FExpr_mul sa a) = "("++show a++".*"++show sa++")"

instance (PCat p cat, PCat (App 'Scalar p) cat) => Functor cat (FExpr Module p) where
    fmap f (FExpr_Module a) = FExpr_Module $ fmap f a
    fmap f (FExpr_mul sa a) = FExpr_mul
        (getPhylumArrow (Proxy::Proxy (App 'Scalar p)) f sa)
        (getPhylumArrow (Proxy::Proxy p)               f a )

instance
    ( GetPhylum p (Expr Module p a) ~ Expr Module p a
    ) => Semigroup (Expr Module p a)
        where
    e1+e2 = Free $ FExpr_Module $ FExpr_plus e1 e2

instance
    ( GetPhylum p (Expr Module p a) ~ Expr Module p a
    , Semigroup (Scalar_ (Expr Module p a))
    ) => Module (Expr Module p a)
        where
    e1.*e2 = Free $ FExpr_mul e2 e1

--------------------

test1 :: Expr Module Id Int
test1 = Free (FExpr_mul
    (Free (FExpr_Module $ FExpr_plus (Pure 3) (Pure 1)))
    (Free (FExpr_Module $ FExpr_plus (Pure 4) (Pure 2)))
    )

test1' :: Expr Module Id Int
test1' = 1.*(2.*4+2).*5+3

sg2mod :: Expr Semigroup Id a -> Expr Module Id a
sg2mod (Pure e) = Pure e
sg2mod (Free (FExpr_plus a1 a2)) = Free $ FExpr_Module $ FExpr_plus (sg2mod a1) (sg2mod a2)
-- sg2mod (Free f) = Free $ FExpr_Module $ _ -- sg2mod f

test1a :: Expr Semigroup Id Int
test1a = Free (FExpr_plus (Pure 3) (Pure 1))

test1b :: Expr Module Id Int
test1b = sg2mod test1a
-- test1b = natFree' q test1a
-- test1b = natFree' (undefined :: cat (FExpr Semigroup a) (FExpr Module a)) test1a

-- q :: Concrete cat => cat (FExpr Semigroup a) (FExpr Module a)
-- q = proveConcrete FExpr_Module
--
-- proveConcrete :: Concrete cat => (a -> b) -> cat a b
-- proveConcrete = undefined
--
-- test1c :: Expr Hask Module Id Int
-- test1c = natFree FExpr_Module test1a

--------------------

newtype WrappedScalar a = WrappedScalar { unwrapScalar :: Scalar a }

instance FAlgebra Hilbert where
    data FExpr Hilbert p a where
        FExpr_Hilbert
            :: {-#UNPACK#-}!(FExpr Module p a)
            -> FExpr Hilbert p a
        FExpr_dp
            :: GetPhylum p a
            -> GetPhylum p a
            -> FExpr Hilbert (App 'Scalar p) a
    type FCxt Hilbert p a = (Module (GetPhylum p a), FCxt_Hilbert p a)
    runFExpr (FExpr_Hilbert e) = runFExpr e
    runFExpr (FExpr_dp a1 a2) = a1<>a2

type family FCxt_Hilbert p a where
    FCxt_Hilbert (App 'Scalar p) a = Hilbert (GetPhylum p a)
    FCxt_Hilbert p               a = Hilbert (GetPhylum p a)

instance
    ( Show (GetPhylum Id a)
    , Show (GetPhylum (App 'Scalar Id) a)
    ) => Show (FExpr Hilbert Id a)
        where
    show (FExpr_Hilbert e) = show e

instance
    ( Show (GetPhylum p a)
    , Show (GetPhylum (App 'Scalar p) a)
    , Scalar (Scalar (GetPhylum p a))~Scalar (GetPhylum p a)
    ) => Show (FExpr Hilbert (App 'Scalar p) a)
        where
    show (FExpr_Hilbert e) = show e
    show (FExpr_dp a1 a2) = "("++show a1++"<>"++show a2++")"

instance (PCat (App 'Scalar p) cat, PCat p cat) => Functor cat (FExpr Hilbert p) where
    fmap f (FExpr_Hilbert e) = FExpr_Hilbert $ fmap f e

instance
    ( PCat (App 'Scalar (App 'Scalar p)) cat
    , PCat (App 'Scalar p) cat
    , PCat p cat
    ) => Functor cat (FExpr Hilbert (App 'Scalar p))
        where
    fmap f (FExpr_Hilbert e) = FExpr_Hilbert $ fmap f e
    fmap f (FExpr_dp a1 a2) = FExpr_dp
        (getPhylumArrow (Proxy::Proxy p) f a1)
        (getPhylumArrow (Proxy::Proxy p) f a2)

instance
    ( GetPhylum p (Expr Hilbert p a) ~ Expr Hilbert p a
    ) => Semigroup (Expr Hilbert p a) where
    e1+e2 = Free $ FExpr_Hilbert $ FExpr_Module $ FExpr_plus e1 e2

instance
    ( GetPhylum p (Expr Hilbert p a) ~ Expr Hilbert p a
    , Semigroup (Scalar_ (Expr Hilbert p a))
    ) => Module (Expr Hilbert p a)
        where
    e1.*e2 = Free $ FExpr_Hilbert $ FExpr_mul e2 e1

instance
    ( Scalar (GetPhylum p (Expr Hilbert ('App 'Scalar p) a)) ~ Expr Hilbert (App 'Scalar p) a
    ,         GetPhylum p (Expr Hilbert ('App 'Scalar p) a)  ~ Expr Hilbert (App 'Scalar p) a
    ) => Hilbert (Expr Hilbert (App 'Scalar p) a)
        where
    e1<>e2 = Free $ FExpr_dp e1 e2

testHilbert :: Expr Hilbert (App 'Scalar Id) Int
testHilbert = (1+(21.*6).*(7.*8))<>(2<>(1 :: Expr Hilbert (App 'Scalar Id) Int))

testHilbert2 = Pure (1,1) <> (Pure (1+1,2) <> (Pure (3,4) :: Expr Hilbert (App 'Scalar Id) (Int,Int)))

testHilbert3 = 1+2 :: Expr Hilbert Id Int

--------------------

-- instance FAlgebra Group where
--     data FExpr Group a
--         = FExpr_Group (FExpr Semigroup a)
--         | FExpr_negate a
--         | FExpr_minus a a
--         deriving Show
--     runFExpr (FExpr_negate a)    = negate a
--     runFExpr (FExpr_minus a1 a2) = a1-a2
--
-- instance Functor Hask (FExpr Group) where
--     fmap f (FExpr_negate a) = FExpr_negate $ f a
--     fmap f (FExpr_minus a1 a2) = FExpr_minus (f a1) (f a2)

-- class (FAlgebra cat cxt1, FAlgebra cat cxt2) => SubAlgebra cat cxt1 cxt2 where
--     liftFAlg :: FExpr cxt1 a -> FExpr cxt2 a
--
-- instance FAlgebra cat cxt1 => SubAlgebra cat cxt1 cxt1 where
--     liftFAlg = id

-- class (cxt a, cxt b) => Sub (cxt :: Type -> Constraint) a b where
--     embed :: Proxy cxt -> a -> b
--
-- instance cxt a => Sub cxt a a where
--     embed _ = P.id
--
-- instance Sub Semigroup Integer Rational where
--     embed _ = P.toRational
--
-- class Pointed a where point :: a
-- instance (Semigroup a, Semigroup b, Pointed b) => Sub Semigroup a (a,b) where
--     embed _ a = (a,point)
--
-- instance (Semigroup a, Semigroup b, Pointed a) => Sub Semigroup b (a,b) where
--     embed _ b = (point,b)

class a <: b where
    embed :: a -> b

instance a <: a where
    embed = P.id

instance Integer <: Rational where
    embed = P.toRational

instance (a,b) <: a where
    embed = P.fst

instance (a,b) <: b where
    embed = P.snd

instance a <: Maybe a where
    embed = Just
    -}
