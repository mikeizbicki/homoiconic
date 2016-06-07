module Algebra2
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

-------------------------------------------------------------------------------

data AT
    = Id
    | Scalar
    | AppAT AT AT

type family AppAT (t::AT) a
type instance AppAT 'Id a = a
type instance AppAT 'Scalar a = Scalar a
type instance AppAT ('AppAT t1 t2) a = AppAT t1 (AppAT t2 a)

--------------------

-- type family PsCatT (ps::[Phylum]) cat where
--     PsCatT '[]    cat = cat
--     PsCatT (p:ps) cat = PCatT p (PsCatT ps cat)

data ATCatT (t::AT) cat a b = ATCatT
    { baseCat :: {-#UNPACK#-}!(cat a b)
    , atCat   :: {-#UNPACK#-}!(AppAT t a -> AppAT t b)
    }

instance Category cat => Category (ATCatT t cat) where
    type ValidObject (ATCatT t cat) a = ValidObject cat a
    id = ATCatT id id
    (ATCatT f1 g1).(ATCatT f2 g2) = ATCatT (f1.f2) (g1.g2)

class Category cat => ATCat (t::AT) cat where
    toAT :: proxy t -> cat a b -> AppAT t a -> AppAT t b

instance Category cat => ATCat t (ATCatT t cat) where
    toAT _ (ATCatT _ g) = g

instance (Category cat, ATCat t' cat) => ATCat t' (ATCatT t cat) where
    toAT t (ATCatT f _) = toAT t f

----------------------------------------

type Expr' cxt a = Expr cxt ('AppAT 'Id 'Id) a

-- FIXME: All these constraints are messed up
eval :: forall cxt t a.
    ( AppAT t (Expr cxt t a) ~ Expr cxt t a
    , AppAT t (AppAT t a) ~ AppAT t a
--     , AppAT 'Scalar (AppAT t a) ~ AppAT t (AppAT 'Scalar a)
--     , AppAT t (AppAT t (Scalar a)) ~ AppAT t (Scalar a)
--     , AppAT t (Expr cxt t (Scalar a)) ~ Free t (FExpr cxt t) (Scalar a)
--     , cxt (UnAppAT t (AppAT t a))
--     , cxt (UnAppAT t (AppAT t (Scalar a)))
    , FAlgebra cxt
--     , Functor (ATCatT t Void2) (FExpr cxt t)
--     (
    ) => ATCatT ('AppAT 'Id t) (ATCatT ('AppAT 'Scalar t) Void2) (Expr cxt t a) (AppAT t a)
eval = (ATCatT (ATCatT Void2 fs) f)
    where
--         fs :: AppAT 'Scalar (Expr cxt t a) -> AppAT 'Scalar (AppAT t a)
--         fs (Pure e) = e
--         fs (Free e) = runFExpr $ fmap' test e

--         f :: AppAT t (Expr cxt t a) -> AppAT t (AppAT t a)
--         f (Pure e) = e
--         f (Free e) = runFExpr $ fmap' test e

        fs = g (Proxy::Proxy 'Scalar) (Proxy::Proxy t)
        f  = g (Proxy::Proxy 'Id    ) (Proxy::Proxy t)

        g :: forall s s'. Proxy s -> Proxy s' -> AppAT s (Expr cxt s' a) -> AppAT s (AppAT s' a)
--         g _ _ (Pure e) = e
        g = undefined

test :: forall cxt t a.
    ( AppAT t (Expr cxt t a) ~ Expr cxt t a
    , AppAT t (AppAT t a) ~ AppAT t a
    , cxt (UnAppAT t (AppAT t a))
    , FAlgebra cxt
    , Functor (ATCatT t Void2) (FExpr cxt t)
    ) => ATCatT t Void2 (Expr cxt t a) (AppAT t a)
test = ATCatT Void2 f
    where
        f :: AppAT t (Expr cxt t a) -> AppAT t (AppAT t a)
        f (Pure e) = e
        f (Free e) = runFExpr $ fmap' test e

evalHask ::
    ( cxt (UnAppAT t (AppAT t a))
    , AppAT t (AppAT t a) ~ AppAT t a
    , FAlgebra cxt
    , Functor Hask (FExpr cxt t)
    ) => Expr cxt t a -> AppAT t a
evalHask (Pure e) = e
evalHask (Free f) = runFExpr $ fmap evalHask f

----------------------------------------
type family UnAppAT (t::AT) a
type instance UnAppAT 'Id a = a
type instance UnAppAT 'Scalar a = a
type instance UnAppAT ('AppAT t1 t2) a = AppAT t2 a

class {-Functor cat (FExpr cxt) =>-} FAlgebra (cxt :: Type -> Constraint) where
    data FExpr cxt (t::AT) (a::Type)
    runFExpr :: cxt (UnAppAT t a) => FExpr cxt t a -> AppAT t a

type instance Scalar (FExpr cxt t a) = FExpr cxt ('AppAT 'Scalar t) a

--------------------------------------------------------------------------------

data Free t f e = Free (f (Free t f e)) | Pure (AppAT t e)

type instance Scalar (Free t f e) = Free t f (Scalar e)

instance (Show (AppAT t e), Show (f (Free t f e))) => Show (Free t f e) where
    show (Pure e) = show e
    show (Free f) = show f

instance Num (AppAT t a) => Num (Free t f a) where
    fromInteger n = Pure $ fromInteger n

--------------------

-- newtype Free' f e = Free' (f (Free' f (Pure f e)))
-- type instance Scalar (Free' f e) = Free' f (Scalar e)
-- type instance Scalar (Pure f e) = Pure f (Scalar e)
--
-- instance Show (f (Free' f (Pure f e))) => Show (Free' f e) where
-- -- instance (Show e, Show (f e)) => Show (Free' f e) where
--     show (Free' f) = show f
--
-- instance (Show e, Show (f e)) => Show (Pure f e) where
--     show (Continue f) = show f
--     show (Pure e) = show e

--------------------

-- type Free t f e = Pure (Fix f) e
--
-- instance Num a => Num (Free t f a) where
--     fromInteger n = Pure $ fromInteger n
--
-- ----------
--
-- newtype Fix f e = Fix (f (Fix f e))
--
-- type instance Scalar (Fix f e) = Fix f (Scalar e)
--
-- instance Show (f (Fix f e)) => Show (Fix f e) where
--     show (Fix f) = trace "a" $ show f
--
-- ----------
--
-- data Pure f e
--     = Continue (f e)
--     | Pure e
--
-- type instance Scalar (Pure f e) = Pure f (Scalar e)
--
-- instance (Show e, Show (f e)) => Show (Pure f e) where
--     show (Continue f) = trace "ba" $ show f
--     show (Pure e) = trace "bb" $ show e

----------------------------------------

type Expr cxt t a = Free t (FExpr cxt t) a

--------------------------------------------------------------------------------

type instance Scalar Int = Int

--------------------------------------------------------------------------------

class Semigroup a where
    (+) :: a -> a -> a

instance FAlgebra Semigroup where
    data FExpr Semigroup t a where
        FExpr_plus
            :: AppAT t a
            -> AppAT t a
            -> FExpr Semigroup ('AppAT 'Id t) a
    runFExpr (FExpr_plus a1 a2) = a1+a2

instance Show (AppAT t a) => Show (FExpr Semigroup ('AppAT 'Id t) a) where
    show (FExpr_plus a1 a2) = "("++show a1++"+"++show a2++")"

instance
    ( Category cat
    ) => Functor
        (ATCatT ('AppAT 'Id t) cat)
        (FExpr Semigroup ('AppAT 'Id t))
        where
    fmap' f (FExpr_plus a1 a2) = FExpr_plus (atCat f a1) (atCat f a2)

-- NOTE:
-- By construction, the constraint for this instance should always be satisfied.
-- But GHC can't automatically prove it for us, so we must write it manually.
instance
    ( AppAT t (Expr Semigroup ('AppAT 'Id t) a)
    ~          Expr Semigroup ('AppAT 'Id t) a
    ) => Semigroup (Expr Semigroup ('AppAT 'Id t) a) where
    a1+a2 = Free $ FExpr_plus a1 a2

instance Semigroup Int where (+) = (P.+)
instance Semigroup Float where (+) = (P.+)

----------------------------------------

class Semigroup a => Module a where
    (.*) :: a -> Scalar a -> a

instance FAlgebra Module where
    data FExpr Module t a where
        FExpr_Module
            :: {-#UNPACK#-}!(FExpr Semigroup t a)
            -> FExpr Module t a
        FExpr_mul
            :: AppAT t a
            -> AppAT 'Scalar (AppAT t a)
            -> FExpr Module ('AppAT 'Id t) a

    runFExpr (FExpr_Module e) = runFExpr e
    runFExpr (FExpr_mul a sa) = a .* sa

instance
    ( Show (AppAT t a)
    , Show (AppAT 'Scalar (AppAT t a))
    ) => Show (FExpr Module ('AppAT 'Id t) a)
        where
    show (FExpr_Module e) = show e
    show (FExpr_mul a sa) = "("++show a++".*"++show sa++")"

instance Functor
    (ATCatT ('AppAT 'Id t) (ATCatT ('AppAT 'Scalar t) Void2))
    (FExpr Module ('AppAT 'Id t))
        where
    fmap' f (FExpr_mul a as) = FExpr_mul (atCat f a) (atCat (baseCat f) as)

instance
    ( AppAT t (Expr Module ('AppAT 'Id t) a)
    ~          Expr Module ('AppAT 'Id t) a
    ) => Semigroup (Expr Module ('AppAT 'Id t) a)
        where
    a1+a2 = Free $ FExpr_Module $ FExpr_plus a1 a2

instance
    ( AppAT t (Expr Module ('AppAT 'Id t) a)
    ~          Expr Module ('AppAT 'Id t) a
    ) => Module (Expr Module ('AppAT 'Id t) a)
        where
    a.*as = Free $ FExpr_mul a as

instance Module Int where (.*) = (P.*)

----------------------------------------

class Module a => Hilbert a where
    (<>) :: a -> a -> Scalar a

instance FAlgebra Hilbert where
    data FExpr Hilbert t a where
        FExpr_Hilbert
            :: {-#UNPACK#-}!(FExpr Module t a)
            -> FExpr Hilbert t a
        FExpr_dp
            :: AppAT t a
            -> AppAT t a
            -> FExpr Hilbert ('AppAT 'Scalar t) a

    runFExpr (FExpr_Hilbert e) = runFExpr e
    runFExpr (FExpr_dp a1 a2) = a1<>a2
