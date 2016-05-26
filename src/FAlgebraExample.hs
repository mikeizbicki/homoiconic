{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE CPP #-}

module FAlgebraExample
    where

import Prelude hiding (Monoid (..),(-),(+),negate,(==),minBound)
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

import Unsafe.Coerce

--------------------------------------------------------------------------------

class Poset a where
    inf :: a -> a -> a

mkFAlgebra ''Poset

#define mkPoset(x) \
instance Poset x where inf = P.min

mkPoset(Float)
mkPoset(Double)
mkPoset(Rational)
mkPoset(Integer)
mkPoset(Int)
mkPoset(Bool)
mkPoset(Char)

instance (Poset a, Poset b) => Poset (a,b) where
    inf (a1,b1) (a2,b2) = (inf a1 a2, inf b1 b2)

----------------------------------------

class Poset a => LowerBounded a where
    minBound :: a

mkFAlgebra ''LowerBounded

#define mkLowerBounded(x) \
instance LowerBounded x where minBound = P.minBound

mkLowerBounded(Bool)
mkLowerBounded(Char)

instance (LowerBounded a, LowerBounded b) => LowerBounded (a,b) where
    minBound = (minBound,minBound)

----------------------------------------

class LowerBounded (Logic a) => Topology a where
    type Logic a
    (==) :: a -> a -> Logic a

mkFAlgebra ''Topology

-- data TLogic
-- type instance App TLogic a = Logic a
--
-- instance FAlgebra Topology where
--     data Sig Topology t a where
--         Sig_Topology_LowerBounded_Logic
--             :: Sig LowerBounded ttt a
--             -> Sig Topology (ttt `Snoc` TLogic) a
--         Sig_eq :: a -> a -> Sig Topology '[TLogic] a
--
--     runSig (p::proxy a) (Sig_Topology_LowerBounded_Logic s)
--         = runSigSnoc (Proxy::Proxy TLogic) (Proxy::Proxy a) s
--
--     runSigTag
--         (p::proxy a)
--         (Sig_Topology_LowerBounded_Logic
--             s::Sig Topology (s:t) (App t a)
--         )
--         = runSigTagSnoc
--             (Proxy::Proxy TLogic)
--             (Proxy::Proxy s)
--             (Proxy::Proxy t)
--             (Proxy::Proxy a)
--             s
--     runSigTag p (Sig_eq e1 e2) = e1==e2
--
--     mape f (Sig_Topology_LowerBounded_Logic s) = Sig_Topology_LowerBounded_Logic $ mape f s
--     mape f (Sig_eq a1 a2) = Sig_eq (f a1) (f a2)
--
-- instance
--     ( View Topology '[TLogic] alg (TLogic ': t)
--     , View LowerBounded '[] alg (TLogic ': t)
--     , View Poset '[] alg (TLogic ': t)
--     , TypeConstraints t a
--     ) => Topology (Free (Sig alg) t a)
--         where
--     type Logic (Free (Sig alg) t a) = Free (Sig alg) (TLogic ': t) a
--     (==) e1 e2 = FreeTag $ embedSig $ Sig_eq e1 e2
--
-- instance View LowerBounded '[] Topology '[TLogic] where
--     embedSig s = Sig_Topology_LowerBounded_Logic s
--     unsafeExtractSig (Sig_Topology_LowerBounded_Logic s)
--         = unsafeCoerceSigTag (Proxy::Proxy '[]) s
-- instance View Poset '[] Topology '[TLogic] where
--     embedSig (s :: Sig Poset '[] a)
--         = Sig_Topology_LowerBounded_Logic (embedSig s :: Sig LowerBounded '[] a)
--     unsafeExtractSig (Sig_Topology_LowerBounded_Logic s)
--         = unsafeExtractSig (unsafeCoerceSigTag (Proxy::Proxy '[]) s)
--
-- instance
--     ( Show a
--     ) => Show (Sig Topology t a) where
--     show (Sig_Topology_LowerBounded_Logic s) = show s
--     show (Sig_eq e1 e2) = show e1++"=="++show e2
--
-- instance {-#OVERLAPS#-} Show (Sig Topology (t0 ': t1 ': t2 ': t3 ': t4 ': '[]) a) where
--     show _ = "<overflow>"

instance Topology Bool where
    type Logic Bool = Bool
    (==) = (P.==)

instance Topology Int where
    type Logic Int = Bool
    (==) = (P.==)

instance (Topology a, Topology b) => Topology (a,b) where
    type Logic (a,b) = (Logic a, Logic b)
    (==) (a1,b1) (a2,b2) = (a1==a2,b1==b2)

----------------------------------------

class Topology a => Semigroup a where
    (+) :: a -> a -> a

mkFAlgebra ''Semigroup

-- instance FAlgebra Semigroup where
--     data Sig Semigroup t a where
--         Sig_Semigroup_Topology_ :: Sig Topology t a -> Sig Semigroup t a
--         Sig_plus :: a -> a -> Sig Semigroup '[] a
--
--     runSig p (Sig_Semigroup_Topology_ s) = runSig p s
--     runSig p (Sig_plus e1 e2) = e1+e2
--
--     runSigTag p (Sig_Semigroup_Topology_ s) = runSigTag p s
--
--     mape f (Sig_Semigroup_Topology_ s) = Sig_Semigroup_Topology_ $ mape f s
--     mape f (Sig_plus e1 e2) = Sig_plus (f e1) (f e2)
--
-- instance
--     ( View Semigroup '[] alg t
--     , View Topology '[TLogic] alg (TLogic ': t)
--     , View LowerBounded '[] alg (TLogic ': t)
--     , View Poset '[] alg (TLogic ': t)
--     , TypeConstraints t a
--     ) => Semigroup (Free (Sig alg) t a)
--         where
--     (+) e1 e2 = Free $ embedSig $ Sig_plus e1 e2
--
-- instance View LowerBounded '[] Semigroup '[TLogic] where
--     embedSig (s :: Sig LowerBounded '[] a)
-- --         = Sig_Semigroup_Topology_ (embedSig s :: Sig Topology '[TLogic] a)
--         = Sig_Semigroup_Topology_ (embedSig s)
--     unsafeExtractSig (Sig_Semigroup_Topology_ s)
--         = unsafeExtractSig (unsafeCoerceSigTag (Proxy::Proxy '[TLogic]) s)
-- instance View Poset '[] Semigroup '[TLogic] where
--     embedSig (s :: Sig Poset '[] a)
--         = Sig_Semigroup_Topology_ (embedSig s :: Sig Topology '[TLogic] a)
--     unsafeExtractSig (Sig_Semigroup_Topology_ s)
--         = unsafeExtractSig (unsafeCoerceSigTag (Proxy::Proxy '[TLogic]) s)
-- instance View Topology '[] Semigroup '[] where
--     embedSig (s :: Sig Topology '[] a)
--         = Sig_Semigroup_Topology_ s
--     unsafeExtractSig (Sig_Semigroup_Topology_ s)
--         = unsafeCoerceSigTag (Proxy::Proxy '[]) s

-- instance View Topology '[TLogic] Semigroup '[TLogic] where
--     embedSig (s :: Sig Topology '[TLogic] a)
--         = Sig_Semigroup_Topology_ s
--     unsafeExtractSig (Sig_Semigroup_Topology_ s)
--         = unsafeCoerceSigTag (Proxy::Proxy '[TLogic]) s

-- instance
--     ( Show a
--     ) => Show (Sig Semigroup t a)
--        where
--     show (Sig_Semigroup_Topology_ s) = show s
--     show (Sig_plus e1 e2) = show e1++"+"++show e2

instance Semigroup Int where (+) = (P.+)
instance (Semigroup a, Semigroup b) => Semigroup (a,b) where
    (a1,b1)+(a2,b2) = (a1+a2,b1+b2)

----------------------------------------

class Semigroup a => Monoid a where
    zero :: a

mkFAlgebra ''Monoid

-- instance View Topology '[TLogic] Monoid '[TLogic] where
--     embedSig (s :: Sig Topology '[TLogic] a)
--         = Sig_Monoid_Semigroup_ (embedSig s :: Sig Semigroup '[TLogic] a)
--     unsafeExtractSig (Sig_Monoid_Semigroup_ s)
--         = unsafeExtractSig $ unsafeCoerceSigTag (Proxy::Proxy '[TLogic]) s

instance Monoid Int where zero = 0
instance (Monoid a, Monoid b) => Monoid (a,b) where
    zero=(zero,zero)

----------------------------------------

type family Scalar a
mkAT ''Scalar

type instance Scalar Int = Int
type instance Scalar (a,b) = Scalar b
type instance Scalar (Free (Sig alg) t a) = Free (Sig alg) (TScalar ': t) a

class (Monoid a, Monoid (Scalar a)) => Module a where
    (.*) :: Scalar a -> a -> a

mkFAlgebra ''Module

-- instance FAlgebra Module where
--     data Sig Module t a where
--         Sig_Module_Monoid_ :: Sig Monoid t a -> Sig Module t a
--         Sig_Module_Monoid_Scalar :: Sig Monoid t a -> Sig Module (t `Snoc` TScalar) a
--         Sig_dotmul :: Scalar a -> a -> Sig Module '[] a
--
--     runSig p (Sig_dotmul e1 e2) = e1.*e2
--     runSig p (Sig_Module_Monoid_ s) = runSig p s
--     runSig (p::proxy a) (Sig_Module_Monoid_Scalar (s::Sig Monoid s b))
--         = runSigSnoc (Proxy::Proxy TScalar) (Proxy::Proxy a) s
--
--     runSigTag p (Sig_Module_Monoid_ s) = runSigTag p s
--
--     mape f (Sig_Module_Monoid_ s) = Sig_Module_Monoid_ $ mape f s
--     mape f (Sig_Module_Monoid_Scalar s) = Sig_Module_Monoid_Scalar $ mape f s
--     mape f (Sig_dotmul a1 a2) = Sig_dotmul (f a1) (f a2)
--
-- instance
--     ( View Monoid '[] alg t
--     , View Monoid '[] alg (TScalar ': t)
--     , View Semigroup '[] alg t
--     , View Semigroup '[] alg (TScalar ': t)
--     , View Module '[] alg t
--     , View Topology '[TLogic] alg (TLogic ': t)
--     , View Topology '[TLogic] alg (TLogic ': TScalar ': t)
--     , View LowerBounded '[] alg (TLogic ': t)
--     , View LowerBounded '[] alg (TLogic ': TScalar ': t)
--     , View Poset '[] alg (TLogic ': t)
--     , View Poset '[] alg (TLogic ': TScalar ': t)
--     ) => Module (Free (Sig alg) t a)
--         where
--     (.*) e1 e2 = Free $ embedSig $ Sig_dotmul e1 e2
--
-- instance View Poset '[] Module '[TLogic,TScalar] where
--     embedSig (s :: Sig Poset '[] a)
--         = Sig_Module_Monoid_Scalar (embedSig s :: Sig Monoid '[TLogic] a)
--     unsafeExtractSig (Sig_Module_Monoid_Scalar s)
--         = unsafeExtractSig $ unsafeCoerceSigTag (Proxy::Proxy '[TLogic]) s
-- instance View LowerBounded '[] Module '[TLogic,TScalar] where
--     embedSig (s :: Sig LowerBounded '[] a)
--         = Sig_Module_Monoid_Scalar (embedSig s :: Sig Monoid '[TLogic] a)
--     unsafeExtractSig (Sig_Module_Monoid_Scalar s)
--         = unsafeExtractSig $ unsafeCoerceSigTag (Proxy::Proxy '[TLogic]) s
-- instance View Poset '[] Module '[TLogic] where
--     embedSig s = Sig_Module_Monoid_ $ embedSig s
--     unsafeExtractSig (Sig_Module_Monoid_ s) = unsafeExtractSig s
-- instance View LowerBounded '[] Module '[TLogic] where
--     embedSig s = Sig_Module_Monoid_ $ embedSig s
--     unsafeExtractSig (Sig_Module_Monoid_ s) = unsafeExtractSig s
-- instance View Topology '[] Module '[TScalar] where
--     embedSig (s :: Sig Topology '[] a)
--         = Sig_Module_Monoid_Scalar (embedSig s :: Sig Monoid '[] a)
--     unsafeExtractSig (Sig_Module_Monoid_Scalar s)
--         = unsafeExtractSig $ unsafeCoerceSigTag (Proxy::Proxy '[]) s
-- instance View Semigroup '[] Module '[TScalar] where
--     embedSig (s :: Sig Semigroup '[] a)
--         = Sig_Module_Monoid_Scalar (embedSig s :: Sig Monoid '[] a)
--     unsafeExtractSig (Sig_Module_Monoid_Scalar s)
--         = unsafeExtractSig $ unsafeCoerceSigTag (Proxy::Proxy '[]) s
-- instance View Monoid '[] Module '[TScalar] where
--     embedSig s = Sig_Module_Monoid_Scalar s
--     unsafeExtractSig (Sig_Module_Monoid_Scalar s) = unsafeCoerceSigTag (Proxy::Proxy '[]) s
-- instance View Topology '[] Module '[] where
--     embedSig s = Sig_Module_Monoid_ $ embedSig s
--     unsafeExtractSig (Sig_Module_Monoid_ s) = unsafeExtractSig s
-- instance View Semigroup '[] Module '[] where
--     embedSig s = Sig_Module_Monoid_ $ embedSig s
--     unsafeExtractSig (Sig_Module_Monoid_ s) = unsafeExtractSig s
-- instance View Monoid '[] Module '[] where
--     embedSig s = Sig_Module_Monoid_ s
--     unsafeExtractSig (Sig_Module_Monoid_ s) = s

-- instance View Topology '[TLogic] Module '[TLogic] where
--     embedSig (s :: Sig Topology '[TLogic] a)
--         = Sig_Module_Monoid_ (embedSig s :: Sig Monoid '[TLogic] a)
--     unsafeExtractSig (Sig_Module_Monoid_ s)
--         = unsafeExtractSig $ unsafeCoerceSigTag (Proxy::Proxy '[TLogic]) s
-- instance View Topology '[TLogic] Module '[TLogic,TScalar] where
--     embedSig (s :: Sig Topology '[TLogic] a)
--         = Sig_Module_Monoid_Scalar_ (embedSig s :: Sig Monoid '[TLogic] a)
--     unsafeExtractSig (Sig_Module_Monoid_Scalar_ s)
--         = unsafeExtractSig $ unsafeCoerceSigTag (Proxy::Proxy '[TLogic]) s

-- instance
--     ( Show a
--     , Show (Scalar a)
--     ) => Show (Sig Module t a)
--         where
--     show (Sig_Module_Monoid_ s) = show s
--     show (Sig_Module_Monoid_Scalar s) = show s
--     show (Sig_dotmul e1 e2) = show e1++".*"++show e2
--
-- instance {-#OVERLAPS#-} Show (Sig Module (t0 ': t1 ': t2 ': t3 ': t4 ': t5 ': '[]) a) where
--     show _ = "<overflow>"

type instance Scalar Bool = Bool

instance Module Int where (.*) = (P.*)
instance (Module a, Module a) => Module (a,a) where
    s.*(a1,b1) = (s.*a1,s.*b1)

----------------------------------------

class Module a => Hilbert a where
    (<>) :: a -> a -> Scalar a

mkFAlgebra ''Hilbert

-- instance FAlgebra Hilbert where
--     data Sig Hilbert t a where
--         Sig_Hilbert_Module_ :: Sig Module t a -> Sig Hilbert t a
--         Sig_ltgt :: a -> a -> Sig Hilbert '[TScalar] a
--
--     runSig p (Sig_Hilbert_Module_ s) = runSig p s
--
--     runSigTag p (Sig_ltgt e1 e2) = e1<>e2
--
--     mape f (Sig_Hilbert_Module_ s) = Sig_Hilbert_Module_ $ mape f s
--     mape f (Sig_ltgt e1 e2) = Sig_ltgt (f e1) (f e2)
--
-- instance View Module '[] Hilbert '[] where
--     embedSig s = Sig_Hilbert_Module_ $ s
-- instance View Semigroup '[] Hilbert '[] where
--     embedSig s = Sig_Hilbert_Module_ $ embedSig s
-- instance View Monoid '[] Hilbert '[] where
--     embedSig s = Sig_Hilbert_Module_ $ embedSig s
-- instance View Semigroup '[] Hilbert '[TScalar] where
--     embedSig s = Sig_Hilbert_Module_ $ embedSig s
-- instance View Monoid '[] Hilbert '[TScalar] where
--     embedSig s = Sig_Hilbert_Module_ $ embedSig s
-- instance View Hilbert '[TScalar] Hilbert '[TScalar] where
--     embedSig (s :: Sig Hilbert '[TScalar] a)
--         = Sig_Hilbert_Module_ (embedSig s :: Sig Module '[TScalar] a)
--     unsafeExtractSig (Sig_Hilbert_Module_ s)
--         = unsafeExtractSig $ unsafeCoerceSigTag (Proxy::Proxy '[TScalar]) s
-- instance View Hilbert '[TScalar] Hilbert '[TScalar,TScalar] where
--     embedSig (s :: Sig Hilbert '[TScalar] a)
--         = Sig_Hilbert_Module_ (embedSig s :: Sig Module '[TScalar,TScalar] a)
--     unsafeExtractSig (Sig_Hilbert_Module_ s)
--         = unsafeExtractSig $ unsafeCoerceSigTag (Proxy::Proxy '[TScalar]) s


-- instance View Topology '[TLogic] Hilbert '[TLogic] where
--     embedSig (s :: Sig Topology '[TLogic] a)
--         = Sig_Hilbert_Module_ (embedSig s :: Sig Module '[TLogic] a)
--     unsafeExtractSig (Sig_Hilbert_Module_ s)
--         = unsafeExtractSig $ unsafeCoerceSigTag (Proxy::Proxy '[TLogic]) s
-- instance View Topology '[TLogic] Hilbert '[TLogic,TScalar] where
--     embedSig (s :: Sig Topology '[TLogic] a)
--         = Sig_Hilbert_Module_ (embedSig s :: Sig Module '[TLogic,TScalar] a)
--     unsafeExtractSig (Sig_Hilbert_Module_ s)
--         = unsafeExtractSig $ unsafeCoerceSigTag (Proxy::Proxy '[TLogic]) s

-- instance
--     ( View Module '[] alg t
--     , View Monoid '[] alg t
--     , View Semigroup '[] alg t
--     , View Monoid '[] alg (TScalar ': t)
--     , View Semigroup '[] alg (TScalar ': t)
--     , View Hilbert '[TScalar] alg (TScalar ': t)
--     , TypeConstraints t a
--     ) => Hilbert (Free (Sig alg) t a) where
--     (<>) e1 e2 = FreeTag $ embedSig $ Sig_ltgt e1 e2
--
-- instance
--     ( Show a
--     , Show (Scalar a)
--     ) => Show (Sig Hilbert t a)
--         where
--     show (Sig_Hilbert_Module_ s) = show s
--     show (Sig_ltgt e1 e2) = show e1++"<>"++show e2
--
-- instance {-#OVERLAPS#-} Show (Sig Hilbert (t0 ': t1 ': t2 ': t3 ': t4 ': '[]) a) where
--     show _ = "<overflow>"

instance Hilbert Int where (<>) = (P.*)
instance Hilbert a => Hilbert (a,a) where
    (a1,b1)<>(a2,b2) = (a1<>a2) + (b1<>b2)

----------------------------------------


class (Hilbert a, Hilbert (Floo a)) => Floobert a where
    type Floo a
    floo :: a -> a

mkFAlgebra ''Floobert

-- data TFloo
--
-- instance FAlgebra Floobert where
--     data Sig Floobert t a where
--         Sig_Floobert_Hilbert_ :: Sig Hilbert t a -> Sig Floobert (t `Snoc` TFloo) a
--         Sig_floo :: a -> Sig Floobert '[] a
--
-- --     runSig p (Sig_Floobert_Hilbert_ s) = runSig p s
--     runSig p (Sig_floo e1) = floo e1
--
--     mape f (Sig_Floobert_Hilbert_ s) = Sig_Floobert_Hilbert_ $ mape f s
--     mape f (Sig_floo e1) = Sig_floo (f e1)
--
-- instance
--     ( View Hilbert '[TScalar] alg (TScalar ': TFloo ': t)
--     , View Floobert '[] alg t
--     , View Module '[] alg (TFloo ': t)
--     , View Monoid '[] alg (TFloo ': t)
--     , View Monoid '[] alg (TScalar ': TFloo ': t)
--     , View Semigroup '[] alg (TFloo ': t)
--     , View Semigroup '[] alg (TScalar ': TFloo ': t)
--     , View Topology '[TLogic] alg (TLogic ': TFloo ': t)
--     , View Topology '[TLogic] alg (TLogic ': TScalar ': TFloo ': t)
--     , View Poset '[] alg (TLogic ': TFloo ': t)
--     , View Poset '[] alg (TLogic ': TScalar ': TFloo ': t)
--     , View LowerBounded '[] alg (TLogic ': TFloo ': t)
--     , View LowerBounded '[] alg (TLogic ': TScalar ': TFloo ': t)
--     , TypeConstraints t a
--     ) => Floobert (Free (Sig alg) t a)
--         where
--     type Floo (Free (Sig alg) t a) = Free (Sig alg) (TFloo ': t) a
--     floo e1 = Free $ embedSig $ Sig_floo e1
--
-- -- instance View Hilbert '[TScalar] Hilbert '[TScalar] where
-- --     embedSig (s :: Sig Hilbert '[TScalar] a)
-- --         = Sig_Hilbert_Module_ (embedSig s :: Sig Module '[TScalar] a)
-- instance View Semigroup '[] Floobert '[] where
--     embedSig (s :: Sig Semigroup '[] a)
--         = Sig_Floobert_Hilbert_ (embedSig s :: Sig Floobert '[TFloo] a)
--
-- instance
--     ( Show a
--     , Show (Scalar a)
-- --     , Show (Scalar a)
-- --     , Show (Sig Hilbert (Init t) a)
--     ) => Show (Sig Floobert t a)
--         where
--     show (Sig_Floobert_Hilbert_ s) = show s
--     show (Sig_floo e1) = "floo "++show e1
--
-- instance {-#OVERLAPS#-} Show (Sig Floobert (t0 ': t1 ': t2 ': t3 ': t4 ': '[]) a) where
--     show _ = "<overflow>"

instance Floobert Int where
    type Floo Int = Int
instance (Hilbert a, Floobert a) => Floobert (a,a) where
    type Floo (a,a) = a

--------------------------------------------------------------------------------

type Space = Floobert

x :: Free (Sig Space) '[] (Int,Int)
x = Pure (1,2)

y :: Free (Sig Space) '[TScalar] (Int,Int)
y = Pure 2

z :: Free (Sig Space) '[TFloo] (Int,Int)
z = Pure 2

type instance TypeConstraints t a = ()

