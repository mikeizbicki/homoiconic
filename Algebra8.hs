-- {-# LANGUAGE UndecidableSuperClasses #-}

module Algebra8
    where

import LocalPrelude
-- import Prelude (Functor(..), Applicative(..), Monad(..))
import qualified Prelude as P

import Unsafe.Coerce

import Data.Kind
import GHC.TypeLits

--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------

class Poset a where
    inf :: a -> a -> a

(&&) :: Poset a => a -> a -> a
(&&) = inf

type family Logic a
-- class Topology a where
class Poset (Logic a) => Topology a where
    (==) :: a -> a -> Logic a

class Topology a => Semigroup a where
    (+) :: a -> a -> a

-- class (Scalar (Scalar a)~Scalar a, Semigroup a) => Module a where
class Semigroup a => Module a where
-- class (Semigroup a, Module (Scalar a)) => Module a where
    type family Scalar a
    (.*) :: Scalar a -> a -> a

class Module a => Hilbert a where
    (<>) :: a -> a -> Scalar a


----------------------------------------

type instance Logic Bool = Bool
instance Poset Bool where
    inf = (P.&&)
instance Topology Bool where
    (==) = (P.==)

type instance Logic Int = Bool
instance Topology Int where
    (==) = (P.==)
instance Semigroup Int where (+) = (P.+)
instance Module Int where
    (.*) = (P.*)
    type Scalar Int = Int
instance Hilbert Int where
    (<>) = (P.*)

type instance Logic (a,b) = (Logic a, Logic b)
instance (Poset a, Poset b) => Poset (a,b) where
    inf (a1,b1) (a2,b2) = (inf a1 a2, inf b1 b2)
instance (Topology a, Topology b) => Topology (a,b) where
    (a1,b1)==(a2,b2) = (a1==a2,b1==b2)
instance (Semigroup a, Semigroup b) => Semigroup (a,b) where
    (a1,b1)+(a2,b2) = (a1+a2,b1+b2)
instance (Module a, Module b, Semigroup (Scalar b), Scalar a~Scalar b) => Module (a,b) where
    type Scalar (a,b) = Scalar b
    s.*(a,b) = (s.*a,s.*b)
instance (Hilbert a, Hilbert b, Semigroup (Scalar b), Scalar a~Scalar b) => Hilbert (a,b) where
    (a1,b1)<>(a2,b2) = (a1<>a2)+(b1<>b2)

--------------------------------------------------------------------------------

x :: Expr Topology 'Id Int
x = Pure 5

y :: Expr Topology 'Id Int
y = Pure 4

--------------------------------------------------------------------------------

type Expr alg = Free (Sig alg)

data Free (f::AT->Type->Type) (t::AT) (a::Type) where
    FreeTag  :: f (     Tag s t  ) (Free f t a)  -> Free f (     Tag s t  ) a
    Free     :: f             t    (Free f t a)  -> Free f             t    a
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
    ShowUntag (f (Tag s   t) (Free f (Tag s   t) a))  = Show (f (Tag s   t) (Free f          t  a))
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
--     go :: Expr alg t a -> App t a
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

eval :: forall alg t a. (FAlgebra alg, alg a) => Expr alg t a -> App t a
eval (Pure    a) = a
eval (Free    s) = alg    (Proxy::Proxy a) $ mape eval s
eval (FreeTag s) = algTag (Proxy::Proxy a) $ mape eval s

----------------------------------------

type instance Logic (Expr alg t a) = Expr alg (Tag 'Logic t) a

class FAlgebra (alg::Type->Constraint) where
    data Sig alg (t::AT) a

    algTag :: alg a => proxy a -> Sig alg (Tag s t) (App t a) -> App (Tag s t) a
    alg    :: alg a => proxy a -> Sig alg        t  (App t a) -> App        t  a

    mape :: (forall t'. Expr alg' t' a -> App t' a)
         -> Sig alg t (Expr alg' t' a)
         -> Sig alg t (App t' a)

--------------------------------------------------------------------------------

instance FAlgebra Poset where
    data Sig Poset t a where
        Si :: a -> a -> Sig Poset 'Id a
    alg _ (Si a1 a2) = inf a1 a2

    mape f (Si e1 e2) = Si (f e1) (f e2)

instance Show a => Show (Sig Poset t a) where
    show (Si a1 a2) = show a1++"&&"++show a2

-- instance Functor_ Hask Hask (Sig Poset t) where
--     fmap f (Si a1 a2) = Si (f a1) (f a2)

instance TagCat 'Id cat1 => Functor_ cat1 Hask (Sig Poset t) where
    fmap f (Si a1 a2) = Si (f $$ a1) (f $$ a2)

instance Poset (Free (Sig Poset) 'Id a) where
    inf e1 e2 = Free $ Si e1 e2

----------------------------------------

instance FAlgebra Topology where
    data Sig Topology t a where
        ST :: {-#UNPACK#-}!(Sig Poset 'Id (Logic a)) -> Sig Topology (Tag 'Logic 'Id) a
        Se :: a -> a -> Sig Topology (Tag 'Logic 'Id) a
        St :: a -> Logic a -> Sig Topology (Tag 'Logic 'Id) a

    algTag p (ST s)     = alg Proxy s
    algTag p (Se a1 a2) = a1==a2

    mape f (ST s) = ST $ mape f s
    mape f (Se e1 e2) = Se (f e1) (f e2)
    mape f (St a la)  = St (f a)  (f la)

instance (Show (Logic a), Show a) => Show (Sig Topology t a) where
    show (ST a) = show a
    show (Se a1 a2) = show a1++"=="++show a2

instance {-#OVERLAPS#-}
    Show (Sig Topology (Tag 'Logic (Tag 'Logic 'Id)) a) where
    show _ = "<<overflow>>"

instance Poset (Expr Topology (Tag 'Logic 'Id) a) where
    inf e1 e2 = FreeTag $ ST $ Si e1 e2

instance Topology (Expr Topology 'Id a) where
--     type Logic (Expr Topology 'Id a) = Expr Topology (Tag 'Logic 'Id) a
    (==) e1 e2 = FreeTag $ Se e1 e2


--------------------------------------------------------------------------------

data AT
    = Id
    | Scalar
    | Logic
    | Tag AT AT

type family App (t::AT) (a::Type) ::  *
type instance App 'Id a = a
type instance App 'Scalar a = Scalar a
type instance App 'Logic  a = Logic  a
type instance App (Tag t t') a = App t (App t' a)

type family MaybeTag (s::AT) (t::AT) where
    MaybeTag 'Scalar (Tag 'Scalar t) = (Tag 'Scalar t)
    MaybeTag s t = Tag s t

type family Nest (t::AT) (a::AT) :: AT where
    Nest 'Id     t       = t
    Nest t       'Id     = t
    Nest 'Scalar (Tag 'Scalar t) = Tag 'Scalar t
    Nest s       (Tag 'Id     t) = Tag s       t
    Nest s       t       = Tag s t
