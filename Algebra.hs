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
import Union
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
    | App Phylum Phylum

type family GetPhylum (p::Phylum) a
type instance GetPhylum Id a = a
type instance GetPhylum 'Scalar a = Scalar a
type instance GetPhylum (App p1 p2) a = GetPhylum p1 (GetPhylum p2 a)

type family CxtPhylum (f::Phylum) a where
    CxtPhylum (App p1 p2) a = GetPhylum p2 a
    CxtPhylum p a           = GetPhylum p  a

type instance Scalar (Expr cxt f a) = Scalar_ (Expr cxt f a)
type family Scalar_ a where
    Scalar_ (Expr cxt (App 'Scalar f) a) = (Expr cxt (App 'Scalar f) a)
    Scalar_ (Expr cxt              f  a) = (Expr cxt (App 'Scalar f) a)

type Expr cxt f a = Free (FExpr cxt f) a

instance Num a => Num (Expr cxt f a) where
    fromInteger n = Pure $ fromInteger n

----------

class {-Functor cat (FExpr cxt) =>-} FAlgebra (cxt :: Type -> Constraint) where
    data FExpr cxt (f::Phylum) (a::Type)
    type FCxt  cxt (f::Phylum) (a::Type) :: Constraint
    runFExpr :: FCxt cxt f a => FExpr cxt f a -> GetPhylum f a
--     runFExpr :: (cxt a, cxt (GetPhylum f a)) => FExpr cxt f a -> GetPhylum f a
--     runFExpr :: cxt (GetPhylum f a) => FExpr cxt f a -> GetPhylum f a

--------------------

data PCatT (p::Phylum) cat a b = PCatT (cat a b) (GetPhylum p a -> GetPhylum p b)

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

--------------------

instance FAlgebra Semigroup where
    data FExpr Semigroup p a where
--         FExpr_Semigroup
--             :: FExpr Topology f a
--             -> FExpr Semigroup f a
        FExpr_plus
            :: GetPhylum p a
            -> GetPhylum p a
            -> FExpr Semigroup p a
    type FCxt Semigroup p a = Semigroup (GetPhylum p a)
    runFExpr (FExpr_plus a1 a2) = a1+a2

instance Show (GetPhylum p a) => Show (FExpr Semigroup p a) where
    show (FExpr_plus a1 a2) = "("++show a1++"+"++show a2++")"

instance PCat p cat => Functor cat (FExpr Semigroup p) where
    fmap f (FExpr_plus a1 a2) = FExpr_plus (getPhylumArrow p f a1) (getPhylumArrow p f a2)
        where
            p = (Proxy::Proxy p)

instance Topology (Expr Semigroup p a) where
    type Neighborhood (Expr Semigroup p a) = ()
    -- FIXME

instance
    ( GetPhylum p (Expr Semigroup p a) ~ Expr Semigroup p a
    ) => Semigroup (Expr Semigroup p a)
        where
    e1+e2 = Free $ FExpr_plus e1 e2


--------------------

instance FAlgebra Module where
    data FExpr Module p a where
        FExpr_Module
            :: FExpr Semigroup p a
            -> FExpr Module p a
        FExpr_mul
            :: GetPhylum (App 'Scalar p) a
            -> GetPhylum p a
            -> FExpr Module p a
    type FCxt Module p a = Module (GetPhylum p a)
    runFExpr (FExpr_Module a) = runFExpr a
    runFExpr (FExpr_mul sa a) = a.*sa

instance
    ( Show (Scalar a)
    , Show (GetPhylum p a)
    , Show (GetPhylum 'Scalar (GetPhylum p a))
    , Show a
    ) => Show (FExpr Module p a)
        where
    show (FExpr_Module e) = show e
    show (FExpr_mul sa a) = "("++show a++".*"++show sa++")"

instance (PCat p cat, PCat (App 'Scalar p) cat) => Functor cat (FExpr Module p) where
    fmap f (FExpr_Module a) = FExpr_Module $ fmap f a
    fmap f (FExpr_mul sa a) = FExpr_mul
        (getPhylumArrow (Proxy::Proxy (App 'Scalar p)) f sa)
        (getPhylumArrow (Proxy::Proxy p)               f a )

instance Topology (Expr Module p a) where
    type Neighborhood (Expr Module p a) = ()
    -- FIXME

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

test1b :: Concrete cat => Expr Module Id Int
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
            :: FExpr Module p a
            -> FExpr Hilbert p a
        FExpr_dp
            :: GetPhylum p a
            -> GetPhylum p a
            -> FExpr Hilbert (App 'Scalar p) a
    type FCxt Hilbert p a = (Module (GetPhylum p a), FCxt_Hilbert p a)
--     type FCxt cat Hilbert f a = Hilbert (GetPhylum f a)
--             :: a
--             -> a
--             -> FExpr Hilbert 'Scalar a
--     type FCxt cat Hilbert f a = (Hilbert a, Hilbert (GetPhylum f a))
    runFExpr (FExpr_Hilbert e) = runFExpr e
    runFExpr (FExpr_dp a1 a2) = a1<>a2

type family FCxt_Hilbert p a where
    FCxt_Hilbert (App 'Scalar p) a = Hilbert (GetPhylum p a)
    FCxt_Hilbert p               a = Hilbert (GetPhylum p a)

instance
    ( Show a
    , Show (Scalar a)
    , Show (GetPhylum Id a)
    , Show (Scalar (GetPhylum Id a))
    ) => Show (FExpr Hilbert Id a)
        where
    show (FExpr_Hilbert e) = show e

instance
    ( Show (GetPhylum p a)
    , Show a
    , Show (Scalar a)
    , Show (Scalar (GetPhylum p a))
    , Scalar (Scalar (GetPhylum p a))~Scalar (GetPhylum p a)
    ) => Show (FExpr Hilbert (App 'Scalar p) a) where
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

instance Topology (Expr Hilbert p a) where
    type Neighborhood (Expr Hilbert p a) = ()
    -- FIXME

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
--     ( Show a
--     , Show (Scalar a)
--     , Scalar (Scalar a)~Scalar a
    ( Scalar (GetPhylum p (Expr Hilbert ('App 'Scalar p) a)) ~ Expr Hilbert (App 'Scalar p) a
    ,         GetPhylum p (Expr Hilbert ('App 'Scalar p) a)  ~ Expr Hilbert (App 'Scalar p) a
    ) => Hilbert (Expr Hilbert (App 'Scalar p) a)
--     ) => Hilbert (Expr Hilbert 'Scalar a)
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

--------------------------------------------------------------------------------

{-
-- instance Topology (Free f) where
--     type Neighborhood (Free f) = ()

--------------------

type Expr cxt b = Free (FExpr cxt) b

test1 :: Expr Semigroup Int
test1 = Free $ FExpr_plus (Pure 5) (Pure 6)

instance Metric Int where
    type Scalar Int = Int

test2 :: FExpr Hilbert Int
test2 = FExpr_dp (3 :: Int)  3

instance Topology b => Topology (Free f b) where
    type Neighborhood (Free f b) = Neighborhood b
instance Metric b => Metric (Free f b) where
    type Scalar (Free f b) = Free f (Scalar b)
instance Poset (Free f b)
instance Topology b => Semigroup (Free f b)
instance Topology b => Hilbert (Free f b)

test3 :: Expr Hilbert Int
test3 = Free ( FExpr_dp (Pure 3) ( Pure (4::Int) :: Free (FExpr Hilbert) Int ))

--------------------

class Functor (CxtHask cxt) (FExpr cxt) => FAlgebra (cxt :: Type -> Constraint) where
    data FExpr cxt a
    runFExpr  :: cxt a  => FExpr cxt a -> a
    showFExpr :: Show a => FExpr cxt a -> String

--------------------

class (Semigroup g) => Hilbert g where
    (<>) :: g -> g -> Scalar g

instance Hilbert Int where (<>) = (P.*)

instance FAlgebra Hilbert where
    data FExpr Hilbert a where
        FExpr_SG :: !(FExpr Semigroup a) -> FExpr Hilbert a
        FExpr_dp :: (Show a, Hilbert a) => a -> a -> FExpr Hilbert (Scalar a)
        -- FIXME:
        -- Does GADT encoding like this result in a lot of runtime overhead?

    runFExpr (FExpr_SG e) = runFExpr e
    runFExpr (FExpr_dp a1 a2) = a1<>a2

    showFExpr (FExpr_SG e) = showFExpr e
    showFExpr (FExpr_dp a1 a2) = show a1++"<>"++show a2

instance Functor (CxtHask Hilbert) (FExpr Hilbert) where

-- FIXME:
-- This can't be a Functor in Hask;
-- but it can be a Functor in a constrained subcategory of Hask.
instance P.Functor (FExpr Hilbert) where
    fmap f (FExpr_SG e) = FExpr_SG $ P.fmap f e
--     fmap f (FExpr_dp a1 a2) = FExpr_dp (f a1) (f a2)

instance Show b => Show (FExpr Hilbert b) where
    show (FExpr_SG g) = show g
    show (FExpr_dp a1 a2) = "FExpr_dp "++show a1++" "++show a2

--------------------

instance FAlgebra Topology where
    data FExpr Topology a where
        FExpr_Eq :: (Topology a) => a -> a -> FExpr Topology (Logic a)

    runFExpr (FExpr_Eq a1 a2) = a1==a2

--     showFExpr (FExpr_Eq a1 a2) = show a1++"=="++show a2

instance Functor (CxtHask Topology) (FExpr Topology) where
    fmap (CxtT (f::a->b)) (FExpr_Eq (a1::a) a2) = _ ((FExpr_Eq::b->b->FExpr Topology (Logic b)) (f a1)) --FExpr_Eq (f a1::b) (f a2::b)

instance P.Functor (FExpr Topology) where
--     fmap f (FExpr_Eq a1 a2) = FExpr_Eq (f a1) (f a2)

instance Show b => Show (FExpr Topology b) where
--     show (FExpr_Eq a1 a2) = "FExpr_Eq "++show a1++" "++show a2

instance (FAlgebra cxt, Topology a) => Topology (FExpr cxt a) where
    type Neighborhood (FExpr cxt a) = Neighborhood a

--------------------

instance FAlgebra Semigroup where
    data FExpr Semigroup a
        = FExpr_Top {-#UNPACK#-}!(FExpr Topology a)
        | FExpr_plus a a
        deriving (Show)
    runFExpr (FExpr_plus a1 a2) = a1+a2
    runFExpr (FExpr_Top e) = runFExpr e

    showFExpr (FExpr_Top e) = showFExpr e
    showFExpr (FExpr_plus a1 a2) = show a1++"<>"++show a2

-- FIXME:
instance Functor (CxtHask Semigroup) (FExpr Semigroup) where
--     fmap f (FExpr_Top e) = FExpr_Top $ fmap f e

instance P.Functor (FExpr Semigroup) where
    fmap f (FExpr_Top e) = FExpr_Top $ P.fmap f e
    fmap f (FExpr_plus a1 a2) = FExpr_plus (f a1) (f a2)

-- instance Show b => Show (Expr Semigroup b) where
--     show (Pure b) = show b
--     show (Free f) = show f

-- instance Semigroup (Expr Semigroup Int) where
--     e1+e2 = Free $ Expr_f $ FExpr_plus e1 e2
    -}
