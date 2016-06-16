{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE CPP #-}

module Heterogeneous.Example
    where

import Prelude hiding (Monoid (..),(-),(+),negate,(==),minBound)
-- import Data.Foldable
-- import Data.List
-- import Data.Typeable
-- import Data.Proxy
import qualified Prelude as P
-- import GHC.Exts

import Test.Tasty
import Test.Tasty.Ingredients.Basic
import Test.Tasty.Options
import Test.Tasty.Runners
import qualified Test.Tasty.SmallCheck as SC
import qualified Test.Tasty.QuickCheck as QC
import Test.QuickCheck hiding (Testable)

import Constrained.FAlgebra
-- import FAlgebra98
-- import Topology
-- import Lattice

import Unsafe.Coerce

--------------------------------------------------------------------------------

class Topology a => Poset a where
-- class Poset a where
    inf :: a -> a -> a

    (<=) :: a -> a -> Logic a
    (<=) a1 a2 = inf a1 a2 == a1

--     (<) :: a -> a -> Logic a
--     (<) a1 a2 = (a1 <= a2)

-- instance FunctorTag (Sig Poset) where
--     fmapTag f (Sig_inf e1 e2) = Sig_inf
--         (apHaskTag (Proxy::Proxy '[]) f e1)
--         (apHaskTag (Proxy::Proxy '[]) f e2)
--
-- type instance ParentClasses '(Poset,t) = '[]
--
-- instance Variety Poset where
--     laws =
--         [ Law
--             { lawName = "commutative"
--             , lhs = inf var1 var2
--             , rhs = inf var2 var1
--             }
--         , Law
--             { lawName = "associative"
--             , lhs = (var1 `inf`  var2) `inf` var3
--             , rhs =  var1 `inf` (var2  `inf` var3)
--             }
--         ]

instance FAlgebra Poset where
    data Sig Poset t a where
        Sig_Poset_Topology_
            :: Sig Topology t a
            -> Sig Poset t a
        Sig_inf :: a -> a -> Sig Poset '[] a

    runSig0 (p::proxy a) (Sig_Poset_Topology_ s)
        = runSig0 (Proxy::Proxy a) s
    runSig0 p (Sig_inf e1 e2) = inf e1 e2

    runSig1
        (p::proxy a)
        (Sig_Poset_Topology_
            s::Sig Poset (s:t) (AppTags t a)
        )
        = runSig1
            p
            s

    mapRun f (Sig_Poset_Topology_ s) = Sig_Poset_Topology_ $ mapRun f s
    mapRun f (Sig_inf e1 e2) = Sig_inf (f e1) (f e2)

instance View Topology '[] Poset '[] where
    embedSig s = Sig_Poset_Topology_ s
    unsafeExtractSig (Sig_Poset_Topology_ s)
        = unsafeCoerceSigTag (Proxy::Proxy '[]) s

instance
    ( View Poset '[] alg (t)
    , View Poset '[] alg (ConsTag TLogic t)
    , View Topology '[TLogic] alg (ConsTag TLogic t)
    , View LowerBounded '[] alg (ConsTag TLogic t)
    , View Poset '[] alg (ConsTag TLogic (ConsTag TLogic t))
    , View Topology '[TLogic] alg (ConsTag TLogic (ConsTag TLogic t))
    , View LowerBounded '[] alg (ConsTag TLogic (ConsTag TLogic t))
--     , TypeConstraints t a
--     , TypeConstraints (ConsTag TLogic t) a
--     , ConsTag TLogic (ConsTag TLogic t) ~ ConsTag TLogic t
    , ConsTag TLogic (ConsTag TLogic (ConsTag TLogic t)) ~ ConsTag TLogic (ConsTag TLogic t)
    , MkFree TLogic t a
    , MkFree TLogic (ConsTag TLogic t) a
    , MkFree TLogic (ConsTag TLogic (ConsTag TLogic t)) a
    ) => Poset (Free (Sig alg) t a)
        where
    inf e1 e2 = Free0 $ embedSig $ Sig_inf e1 e2

instance
    ( Show a
    ) => Show (Sig Poset t a) where
    show (Sig_Poset_Topology_ s) = show s
    show (Sig_inf e1 e2) = "inf "++show e1++" "++show e2

#define mkPoset(x) \
instance Poset x where inf = P.min

-- mkPoset(Float)
-- mkPoset(Double)
-- mkPoset(Rational)
-- mkPoset(Integer)
-- mkPoset(Int)
mkPoset(Bool)
-- mkPoset(Char)

instance (Poset a, Poset b) => Poset (a,b) where
    inf (a1,b1) (a2,b2) = (inf a1 a2, inf b1 b2)

----------------------------------------

class Poset a => LowerBounded a where
    minBound :: a

-- instance FunctorTag (Sig LowerBounded) where
--     fmapTag f (Sig_LowerBounded_Poset_ s) = Sig_LowerBounded_Poset_ $ fmapTag f s
--     fmapTag f (Sig_minBound) = Sig_minBound
--
-- type instance ParentClasses '(LowerBounded,t) =
--     '[ '(Poset,t)
--      ]
--
-- instance Variety LowerBounded where
--     laws =
--         [ Law
--             { lawName = "minBound"
--             , lhs = inf minBound var1
--             , rhs = minBound
--             }
--         ]

instance FAlgebra LowerBounded where
    data Sig LowerBounded t a where
        Sig_LowerBounded_Poset_
            :: Sig Poset t a
            -> Sig LowerBounded t a
        Sig_minBound :: Sig LowerBounded '[] a

    runSig0 (p::proxy a) (Sig_LowerBounded_Poset_ s)
        = runSig0 (Proxy::Proxy a) s
    runSig0 p Sig_minBound = minBound

    runSig1
        (p::proxy a)
        (Sig_LowerBounded_Poset_
            s::Sig LowerBounded (s:t) (AppTags t a)
        )
        = runSig1
            p
            s

    mapRun f (Sig_LowerBounded_Poset_ s) = Sig_LowerBounded_Poset_ $ mapRun f s
    mapRun f Sig_minBound = Sig_minBound

instance View Poset '[] LowerBounded '[] where
    embedSig s = Sig_LowerBounded_Poset_ s
    unsafeExtractSig (Sig_LowerBounded_Poset_ s)
        = unsafeCoerceSigTag (Proxy::Proxy '[]) s

instance
    ( View LowerBounded '[] alg (t)
    , View Poset '[] alg (t)
    , View Poset '[] alg (ConsTag TLogic t)
    , View Topology '[TLogic] alg (ConsTag TLogic t)
    , View LowerBounded '[] alg (ConsTag TLogic t)
    , View LowerBounded '[] alg (ConsTag TLogic (ConsTag TLogic t))
    , View Poset '[] alg (ConsTag TLogic (ConsTag TLogic t))
    , View Topology '[TLogic] alg (ConsTag TLogic (ConsTag TLogic t))
--     , TypeConstraints t a
--     , TypeConstraints (ConsTag TLogic t) a
--     , ConsTag TLogic (ConsTag TLogic t) ~ ConsTag TLogic t
    , ConsTag TLogic (ConsTag TLogic (ConsTag TLogic t)) ~ ConsTag TLogic (ConsTag TLogic t)
--     , ConsTag TLogic t ~ (TLogic : t)
    , MkFree TLogic t a
    , MkFree TLogic (ConsTag TLogic t) a
    , MkFree TLogic (ConsTag TLogic (ConsTag TLogic t)) a
    ) => LowerBounded (Free (Sig alg) t a)
        where
    minBound = Free0 $ embedSig $ Sig_minBound

instance
    ( Show a
    ) => Show (Sig LowerBounded t a) where
    show (Sig_LowerBounded_Poset_ s) = show s
    show Sig_minBound = "minBound"

#define mkLowerBounded(x) \
instance LowerBounded x where minBound = P.minBound

mkLowerBounded(Bool)
-- mkLowerBounded(Char)

instance (LowerBounded a, LowerBounded b) => LowerBounded (a,b) where
    minBound = (minBound,minBound)

----------------------------------------

-- type ValidLogic a = Logic (Logic (Logic (Logic a))) ~ (Logic (Logic (Logic a)))
type ValidLogic a = Logic (Logic (Logic a)) ~ Logic (Logic a)

class (LowerBounded (Logic a), ValidLogic a) => Topology a where
-- class (LowerBounded (Logic a), Logic (Logic (Logic a))~Logic (Logic a)) => Topology a where
-- class (LowerBounded (Logic a), Logic (Logic a)~(Logic a)) => Topology a where
-- class (LowerBounded (Logic a)) => Topology a where
    type Logic a
    (==) :: a -> a -> Logic a

-- instance FunctorTag (Sig Topology) where
--     fmapTag f (Sig_Topology_LowerBounded_Logic_ s) = Sig_Topology_LowerBounded_Logic_ $ fmapTag f s
--     fmapTag f (Sig_eqeq e1 e2) = Sig_eqeq
--         (apHaskTag (Proxy::Proxy '[]) f e1)
--         (apHaskTag (Proxy::Proxy '[]) f e2)

data TLogic
type instance AppTag TLogic a = Logic a

-- type instance TypeConstraints (TLogic ': t) a = ()
-- type family ConsTag TLogic t where
--     ConsTag TLogic t = TLogic : t

-- type instance TypeConstraints (TLogic ': t) a = TypeConstraints_TLogic t a
-- type instance TypeConstraints (TLogic ': t) a = ()
-- type instance TypeConstraints (TLogic ': t) a
--     = AppTags (ConsTag TLogic t) a ~ AppTags t a

-- type family TypeConstraints_TLogic t a :: Constraint where
-- --     TypeConstraints_TLogic (TLogic ': t) a = ()
--     TypeConstraints_TLogic (TLogic ': t) a = TypeConstraints_TLogic t a
--     TypeConstraints_TLogic t a = ()

type instance ConsTag TLogic ts = ConsTag_TLogic ts

type family ConsTag_TLogic t where
--     ConsTag_TLogic (TLogic ': t) = TLogic ': t
    ConsTag_TLogic (TLogic : TLogic : t) = TLogic : TLogic : t
    ConsTag_TLogic                    t  = TLogic : t

instance FAlgebra Topology where
    data Sig Topology t a where
        Sig_Topology_LowerBounded_Logic_
            :: Sig LowerBounded t a
            -> Sig Topology (t `Snoc` TLogic) a
        Sig_eqeq :: a -> a -> Sig Topology '[TLogic] a

    runSig0 (p::proxy a) (Sig_Topology_LowerBounded_Logic_ s)
        = runSig0Snoc (Proxy::Proxy TLogic) (Proxy::Proxy a) s

    runSig1
        (p::proxy a)
        (Sig_Topology_LowerBounded_Logic_
            s::Sig Topology (s:t) (AppTags t a)
        )
        = runSig1Snoc
            (Proxy::Proxy TLogic)
            (Proxy::Proxy s)
            (Proxy::Proxy t)
            (Proxy::Proxy a)
            s
    runSig1 p (Sig_eqeq e1 e2) = e1==e2

    mapRun f (Sig_Topology_LowerBounded_Logic_ s) = Sig_Topology_LowerBounded_Logic_ $ mapRun f s
    mapRun f (Sig_eqeq a1 a2) = Sig_eqeq (f a1) (f a2)

instance
    ( View Topology     '[TLogic]   alg (ConsTag TLogic t)
    , View LowerBounded '[]         alg (ConsTag TLogic t)
    , View Poset        '[]         alg (ConsTag TLogic t)
    , View Topology     '[TLogic]   alg (ConsTag TLogic (ConsTag TLogic t))
    , View LowerBounded '[]         alg (ConsTag TLogic (ConsTag TLogic t))
    , View Poset        '[]         alg (ConsTag TLogic (ConsTag TLogic t))
--     , TypeConstraints t a
--     , TypeConstraints (ConsTag TLogic t) a
--     , ConsTag TLogic (ConsTag TLogic t) ~ ConsTag TLogic t
    , ConsTag TLogic (ConsTag TLogic (ConsTag TLogic t)) ~ ConsTag TLogic (ConsTag TLogic t)
    , MkFree TLogic t a
    , MkFree TLogic (ConsTag TLogic t) a
    , MkFree TLogic (ConsTag TLogic (ConsTag TLogic t)) a
    ) => Topology (Free (Sig alg) t a)
        where
    type Logic (Free (Sig alg) t a) = Free (Sig alg) (ConsTag TLogic t) a
    (==) e1 e2 = mkMkFree (Proxy::Proxy TLogic) $ embedSig $ Sig_eqeq e1 e2

class MkFree s (t::[Tag]) a where
    mkMkFree :: proxy s -> f (ConsTag TLogic t) (Free f t a) -> Free f (ConsTag TLogic t) a

instance MkFree TLogic (TLogic : TLogic : t) a where
    mkMkFree _ = Free0

instance MkFree TLogic (TLogic : '[]) a where
    mkMkFree _ = Free1

instance MkFree TLogic '[] a where
    mkMkFree _ = Free1

instance View Poset '[] Topology '[TLogic,TLogic] where
    embedSig (s :: Sig Poset '[] a)
        = Sig_Topology_LowerBounded_Logic_ (embedSig s :: Sig LowerBounded '[TLogic] a)
instance View LowerBounded '[] Topology '[TLogic,TLogic] where
    embedSig (s :: Sig LowerBounded '[] a)
        = Sig_Topology_LowerBounded_Logic_ (embedSig s :: Sig LowerBounded '[TLogic] a)
instance View Topology '[TLogic] Topology '[TLogic,TLogic] where
    embedSig (s :: Sig Topology '[TLogic] a)
        = Sig_Topology_LowerBounded_Logic_ (embedSig s :: Sig LowerBounded '[TLogic] a)

instance View Poset '[] LowerBounded '[TLogic] where
    embedSig (s :: Sig Poset '[] a)
        = Sig_LowerBounded_Poset_ (embedSig s :: Sig Poset '[TLogic] a)
instance View LowerBounded '[] LowerBounded '[TLogic] where
    embedSig (s :: Sig LowerBounded '[] a)
        = Sig_LowerBounded_Poset_ (embedSig s :: Sig Poset '[TLogic] a)
instance View Topology '[TLogic] LowerBounded '[TLogic] where
    embedSig (s :: Sig Topology '[TLogic] a)
        = Sig_LowerBounded_Poset_ (embedSig s :: Sig Poset '[TLogic] a)
instance View Poset '[] LowerBounded '[TLogic,TLogic] where
    embedSig (s :: Sig Poset '[] a)
        = Sig_LowerBounded_Poset_ (embedSig s :: Sig Poset '[TLogic,TLogic] a)
instance View LowerBounded '[] LowerBounded '[TLogic,TLogic] where
    embedSig (s :: Sig LowerBounded '[] a)
        = Sig_LowerBounded_Poset_ (embedSig s :: Sig Poset '[TLogic,TLogic] a)
instance View Topology '[TLogic] LowerBounded '[TLogic,TLogic] where
    embedSig (s :: Sig Topology '[TLogic] a)
        = Sig_LowerBounded_Poset_ (embedSig s :: Sig Poset '[TLogic,TLogic] a)

instance View Poset '[] Poset '[TLogic] where
    embedSig (s :: Sig Poset '[] a)
        = Sig_Poset_Topology_ (embedSig s :: Sig Topology '[TLogic] a)
instance View LowerBounded '[] Poset '[TLogic] where
    embedSig (s :: Sig LowerBounded '[] a)
        = Sig_Poset_Topology_ (embedSig s :: Sig Topology '[TLogic] a)
instance View Topology '[TLogic] Poset '[TLogic] where
    embedSig (s :: Sig Topology '[TLogic] a)
        = Sig_Poset_Topology_ (embedSig s :: Sig Topology '[TLogic] a)
instance View Poset '[] Poset '[TLogic,TLogic] where
    embedSig (s :: Sig Poset '[] a)
        = Sig_Poset_Topology_ (embedSig s :: Sig Topology '[TLogic,TLogic] a)
instance View LowerBounded '[] Poset '[TLogic,TLogic] where
    embedSig (s :: Sig LowerBounded '[] a)
        = Sig_Poset_Topology_ (embedSig s :: Sig Topology '[TLogic,TLogic] a)
instance View Topology '[TLogic] Poset '[TLogic,TLogic] where
    embedSig (s :: Sig Topology '[TLogic] a)
        = Sig_Poset_Topology_ (embedSig s :: Sig Topology '[TLogic,TLogic] a)

instance View LowerBounded '[] Topology '[TLogic] where
    embedSig s = Sig_Topology_LowerBounded_Logic_ s
    unsafeExtractSig (Sig_Topology_LowerBounded_Logic_ s)
        = unsafeCoerceSigTag (Proxy::Proxy '[]) s
instance View Poset '[] Topology '[TLogic] where
    embedSig (s :: Sig Poset '[] a)
        = Sig_Topology_LowerBounded_Logic_ (embedSig s :: Sig LowerBounded '[] a)
    unsafeExtractSig (Sig_Topology_LowerBounded_Logic_ s)
        = unsafeExtractSig (unsafeCoerceSigTag (Proxy::Proxy '[]) s)

instance
    ( Show a
    ) => Show (Sig Topology t a) where
    show (Sig_Topology_LowerBounded_Logic_ s) = show s
    show (Sig_eqeq e1 e2) = show e1++"=="++show e2

instance {-#OVERLAPS#-} Show (Sig Topology (t0 ': t1 ': t2 ': t3 ': t4 ': '[]) a) where
    show _ = "<overflow>"

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

-- instance FunctorTag (Sig Semigroup) where
--     fmapTag f (Sig_Semigroup_Topology_ s) = Sig_Semigroup_Topology_ $ fmapTag f s
--     fmapTag f (Sig_plus e1 e2) = Sig_plus
--         (apHaskTag (Proxy::Proxy '[]) f e1)
--         (apHaskTag (Proxy::Proxy '[]) f e2)

-- instance FAlgebra Semigroup where
--     data Sig Semigroup t a where
--         Sig_Semigroup_Topology_ :: Sig Topology t a -> Sig Semigroup t a
--         Sig_plus :: a -> a -> Sig Semigroup '[] a
--
--     runSig0 p (Sig_Semigroup_Topology_ s) = runSig0 p s
--     runSig0 p (Sig_plus e1 e2) = e1+e2
--
--     runSig1 p (Sig_Semigroup_Topology_ s) = runSig1 p s
--
--     mapRun f (Sig_Semigroup_Topology_ s) = Sig_Semigroup_Topology_ $ mapRun f s
--     mapRun f (Sig_plus e1 e2) = Sig_plus (f e1) (f e2)
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

-- instance FunctorTag (Sig Monoid) where
--     fmapTag f (Sig_Monoid_Semigroup_ s) = Sig_Monoid_Semigroup_ $ fmapTag f s
--     fmapTag f (Sig_zero) = Sig_zero

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
mkTag ''Scalar
-- mkTagIdempotent ''Scalar

type instance Scalar (Free (Sig alg) t a) = Free (Sig alg) (TScalar ': t) a

-- type instance Scalar (Free (Sig alg) t a) = Free (Sig alg) (Cons_TScalar t) a
type instance Scalar Var = Var
-- -- type instance Logic Var = Var
--
-- type instance AppTag TScalar a = Scalar a
--
-- -- data TScalar
-- type instance TypeConstraints (TScalar ': t) a
--     = (AppTags (Cons_TScalar t) a~Scalar (AppTags t a), TypeConstraints_TScalar t a)
--
-- type family TypeConstraints_TScalar t a :: Constraint where
-- --     TypeConstraints_TScalar (TScalar ': t) a = ()
--     TypeConstraints_TScalar (TScalar ': t) a = TypeConstraints_TScalar t a
--     TypeConstraints_TScalar t a = ()
--
-- type family Cons_TScalar t where
--     Cons_TScalar (TScalar ': t) = TScalar ': t
--     Cons_TScalar             t  = TScalar ': t


-- class (Monoid a, Module (Scalar a), Scalar (Scalar a)~Scalar a) => Module a where
-- class (Monoid a, Module (Scalar a)) => Module a where
-- class (Scalar (Scalar a)~Scalar a) => Module a where
class (Monoid a, Monoid (Scalar a)) => Module a where
--     type Scalar a
    (.*) :: Scalar a -> a -> a

-- instance FunctorTag (Sig Module) where
--     fmapTag f (Sig_Module_Monoid_ s)       = Sig_Module_Monoid_ $ fmapTag f s
--     fmapTag f (Sig_Module_Monoid_Scalar_ s) = Sig_Module_Monoid_Scalar_ $ fmapTag f s
--     fmapTag f (Sig_dotmul e1 e2) = Sig_dotmul
--         (apHaskTag (Proxy::Proxy '[TScalar]) f e1)
--         (apHaskTag (Proxy::Proxy '[]       ) f e2)

{-

instance FAlgebra Module where
    data Sig Module t a where
        Sig_Module_Monoid_ :: Sig Monoid t a -> Sig Module t a
        Sig_Module_Module_Scalar_ :: Sig Module t a -> Sig Module (t `Snoc` TScalar) a
        Sig_dotmul :: Scalar a -> a -> Sig Module '[] a

    runSig0 p (Sig_dotmul e1 e2) = e1.*e2
    runSig0 p (Sig_Module_Monoid_ s) = runSig0 p s
    runSig0 (p::proxy a) (Sig_Module_Module_Scalar_ s)
        = runSig0Snoc (Proxy::Proxy TScalar) (Proxy::Proxy a) s

    runSig1 p (Sig_Module_Monoid_ s) = runSig1 p s

    mapRun f (Sig_Module_Monoid_ s) = Sig_Module_Monoid_ $ mapRun f s
    mapRun f (Sig_Module_Module_Scalar_ s) = Sig_Module_Module_Scalar_ $ mapRun f s
    mapRun f (Sig_dotmul a1 a2) = Sig_dotmul (unsafeCoerce f a1) (f a2)

instance
    ( View Monoid '[] alg t
    , View Monoid '[] alg (Cons_TScalar t)
    , View Semigroup '[] alg t
    , View Semigroup '[] alg (Cons_TScalar t)
    , View Module '[] alg t
    , View Topology '[TLogic] alg (TLogic ': t)
    , View Topology '[TLogic] alg (TLogic ': Cons_TScalar t)
    , View LowerBounded '[] alg (TLogic ': t)
    , View LowerBounded '[] alg (TLogic ': Cons_TScalar t)
    , View Poset '[] alg (TLogic ': t)
    , View Poset '[] alg (TLogic ': Cons_TScalar t)
    , View Module '[] alg (Cons_TScalar t)
    , TypeConstraints t a
    , TypeConstraints (Cons_TScalar t) a
    , Cons_TScalar (Cons_TScalar t) ~ Cons_TScalar t
    ) => Module (Free (Sig alg) t a)
        where
--     type Scalar (Free (Sig alg) t a) = Free (Sig alg) (Cons_TScalar t) a
    (.*) e1 e2 = Free0 $ embedSig $ Sig_dotmul e1 e2

instance View Poset '[] Module '[TLogic,TScalar] where
    embedSig (s :: Sig Poset '[] a)
        = Sig_Module_Module_Scalar_ (embedSig s :: Sig Module '[TLogic] a)
    unsafeExtractSig (Sig_Module_Module_Scalar_ s)
        = unsafeExtractSig $ unsafeCoerceSigTag (Proxy::Proxy '[TLogic]) s
instance View LowerBounded '[] Module '[TLogic,TScalar] where
    embedSig (s :: Sig LowerBounded '[] a)
        = Sig_Module_Module_Scalar_ (embedSig s :: Sig Module '[TLogic] a)
    unsafeExtractSig (Sig_Module_Module_Scalar_ s)
        = unsafeExtractSig $ unsafeCoerceSigTag (Proxy::Proxy '[TLogic]) s
instance View Poset '[] Module '[TLogic] where
    embedSig s = Sig_Module_Monoid_ $ embedSig s
    unsafeExtractSig (Sig_Module_Monoid_ s) = unsafeExtractSig s
instance View LowerBounded '[] Module '[TLogic] where
    embedSig s = Sig_Module_Monoid_ $ embedSig s
    unsafeExtractSig (Sig_Module_Monoid_ s) = unsafeExtractSig s
instance View Topology '[] Module '[TScalar] where
    embedSig (s :: Sig Topology '[] a)
        = Sig_Module_Module_Scalar_ (embedSig s :: Sig Module '[] a)
    unsafeExtractSig (Sig_Module_Module_Scalar_ s)
        = unsafeExtractSig $ unsafeCoerceSigTag (Proxy::Proxy '[]) s
instance View Semigroup '[] Module '[TScalar] where
    embedSig (s :: Sig Semigroup '[] a)
        = Sig_Module_Module_Scalar_ (embedSig s :: Sig Module '[] a)
    unsafeExtractSig (Sig_Module_Module_Scalar_ s)
        = unsafeExtractSig $ unsafeCoerceSigTag (Proxy::Proxy '[]) s
instance View Monoid '[] Module '[TScalar] where
    embedSig (s :: Sig Monoid '[] a)
        = Sig_Module_Module_Scalar_ (embedSig s :: Sig Module '[] a)
    unsafeExtractSig (Sig_Module_Module_Scalar_ s)
        = unsafeExtractSig $ unsafeCoerceSigTag (Proxy::Proxy '[]) s
instance View Module '[] Module '[TScalar] where
    embedSig s = Sig_Module_Module_Scalar_ s
    unsafeExtractSig (Sig_Module_Module_Scalar_ s) = unsafeCoerceSigTag (Proxy::Proxy '[]) s
instance View Topology '[] Module '[] where
    embedSig s = Sig_Module_Monoid_ $ embedSig s
    unsafeExtractSig (Sig_Module_Monoid_ s) = unsafeExtractSig s
instance View Semigroup '[] Module '[] where
    embedSig s = Sig_Module_Monoid_ $ embedSig s
    unsafeExtractSig (Sig_Module_Monoid_ s) = unsafeExtractSig s
instance View Monoid '[] Module '[] where
    embedSig s = Sig_Module_Monoid_ s
    unsafeExtractSig (Sig_Module_Monoid_ s) = s

instance View Topology '[TLogic] Module '[TLogic] where
    embedSig (s :: Sig Topology '[TLogic] a)
        = Sig_Module_Monoid_ (embedSig s :: Sig Monoid '[TLogic] a)
    unsafeExtractSig (Sig_Module_Monoid_ s)
        = unsafeExtractSig $ unsafeCoerceSigTag (Proxy::Proxy '[TLogic]) s
instance View Topology '[TLogic] Module '[TLogic,TScalar] where
    embedSig (s :: Sig Topology '[TLogic] a)
        = Sig_Module_Module_Scalar_ (embedSig s :: Sig Module '[TLogic] a)
    unsafeExtractSig (Sig_Module_Module_Scalar_ s)
        = unsafeExtractSig $ unsafeCoerceSigTag (Proxy::Proxy '[TLogic]) s

instance
    ( Show a
    , Show (Scalar a)
    , Show (Logic a)
    ) => Show (Sig Module t a)
        where
    show (Sig_Module_Monoid_ s) = show s
    show (Sig_Module_Module_Scalar_ s) = show s
    show (Sig_dotmul e1 e2) = show e1++".*"++show e2

instance {-#OVERLAPS#-} Show (Sig Module (t0 ': t1 ': t2 ': t3 ': t4 ': t5 ': '[]) a) where
    show _ = "<overflow>"
-}

type instance Scalar Bool = Bool

type instance Scalar Int = Int
type instance Scalar (a,b) = Scalar b

instance Module Int where
    (.*) = (P.*)
--     type Scalar Int = Int

instance (Module a, Module a) => Module (a,a) where
--     type Scalar (a,a) = Scalar a
    s.*(a1,b1) = (s.*a1,s.*b1)

----------------------------------------

class Module a => Hilbert a where
    (<>) :: a -> a -> Scalar a

-- instance FunctorTag (Sig Hilbert) where
--     fmapTag f (Sig_Hilbert_Module_ s) = Sig_Hilbert_Module_ $ fmapTag f s
--     fmapTag f (Sig_ltgt e1 e2) = Sig_ltgt
--         (apHaskTag (Proxy::Proxy '[]) f e1)
--         (apHaskTag (Proxy::Proxy '[]) f e2)

-- instance FAlgebra Hilbert where
--     data Sig Hilbert t a where
--         Sig_Hilbert_Module_ :: Sig Module t a -> Sig Hilbert t a
--         Sig_ltgt :: a -> a -> Sig Hilbert '[TScalar] a
--
--     runSig0 p (Sig_Hilbert_Module_ s) = runSig0 p s
--
--     runSig1 p (Sig_ltgt e1 e2) = e1<>e2
--
--     mapRun f (Sig_Hilbert_Module_ s) = Sig_Hilbert_Module_ $ mapRun f s
--     mapRun f (Sig_ltgt e1 e2) = Sig_ltgt (f e1) (f e2)
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
--     (<>) e1 e2 = Free1 $ embedSig $ Sig_ltgt e1 e2
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

-- instance FunctorTag (Sig Floobert) where
--     fmapTag f (Sig_Floobert_Hilbert_ s) = Sig_Floobert_Hilbert_ $ fmapTag f s
--     fmapTag f (Sig_floo e1) = Sig_floo
--         (apHaskTag (Proxy::Proxy '[]) f e1)

-- data TFloo
--
-- instance FAlgebra Floobert where
--     data Sig Floobert t a where
--         Sig_Floobert_Hilbert_ :: Sig Hilbert t a -> Sig Floobert (t `Snoc` TFloo) a
--         Sig_floo :: a -> Sig Floobert '[] a
--
-- --     runSig0 p (Sig_Floobert_Hilbert_ s) = runSig0 p s
--     runSig0 p (Sig_floo e1) = floo e1
--
--     mapRun f (Sig_Floobert_Hilbert_ s) = Sig_Floobert_Hilbert_ $ mapRun f s
--     mapRun f (Sig_floo e1) = Sig_floo (f e1)
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

-- mkFAlgebra ''Topology
-- mkFAlgebra ''Hilbert

type Space = Topology

u :: Free (Sig Space) '[] Int
u = Pure 1

x :: Free (Sig Space) '[] (Int,Int)
x = Pure (1,2)

y :: Free (Sig Space) '[TScalar] (Int,Int)
y = Pure 2

-- z :: Free (Sig Space) '[TFloo] (Int,Int)
-- z = Pure 2
