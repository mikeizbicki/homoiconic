{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}

module Algebra4
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
-- import GHC.Generics

import Unsafe.Coerce

-------------------------------------------------------------------------------

class Semigroup a where
    (+) :: a -> a -> a

type ValidScalar a = (Scalar a~a, Module a)

-- class (ValidScalar (Scalar a), Semigroup a) => Module a where
class Semigroup a => Module a where
    (.*) :: a -> Scalar a -> a

class Module a => Hilbert a where
    (<>) :: a -> a -> Scalar a

--------------------------------------------------------------------------------

unTag :: e (TagAT t1 t2) a -> e (NestAT t1 t2) a
unTag = unsafeCoerce

reTag :: e (NestAT t1 t2) a -> e (TagAT t1 t2) a
reTag = unsafeCoerce

--------------------------------------------------------------------------------

instance (Show (AppAT t a), Num (AppAT t a)) => Num (G Semigroup 'Id t a)
    where fromInteger = Gi . fromInteger
instance (Show (AppAT t a), Num (AppAT t a)) => Num (G Module 'Id t a)
    where fromInteger = GM . fromInteger
-- instance (Show (AppAT t a), Num (AppAT t a)) => Num (G Hilbert t a)
--     where fromInteger = GH . fromInteger

type instance Scalar (G cxt s t a) = G cxt s (NestAT 'Scalar t) a

--------------------

class GAlgebra (alg::Type->Constraint) where
    data G alg (s::AT) (t::AT) a
    runG :: alg (AppAT t a) => G alg s t a -> AppAT (TagAT s t) a
    mkG :: AppAT t a -> G alg 'Id t a

class (GAlgebra cxt1, GAlgebra cxt2) => EmbedG cxt1 s cxt2 where
    embedG :: G cxt2 s t a -> G cxt1 s t a

instance GAlgebra cxt => EmbedG cxt 'Id cxt where
    embedG a = a

--------------------

instance GAlgebra Semigroup where
    data G Semigroup s t a where
        Gi :: AppAT t a -> G Semigroup 'Id t a
        Gp ::
            ( EmbedG Semigroup 'Id cxt
            ) => G cxt 'Id t a
              -> G cxt 'Id t a
              -> G Semigroup 'Id t a

    runG (Gi a) = a
    runG (Gp a1 a2) = runG a1' + runG a2'
        where
            a1' = embedG @Semigroup @'Id a1
            a2' = embedG @Semigroup @'Id a2

    mkG = Gi

instance Semigroup (G Semigroup 'Id t a) where (+) e1 e2 = Gp e1 e2

instance Show (AppAT t a) => Show (G Semigroup s t a) where
    show (Gi a) = show a
    show (Gp a1 a2) = "("++show a1'++"+"++show a2'++")"
        where
            a1' = embedG @Semigroup @'Id a1
            a2' = embedG @Semigroup @'Id a2

--------------------

instance GAlgebra Module where
    data G Module s t a where
        GM  :: {-#UNPACK#-}!(G Semigroup s t a) -> G Module s t a
        Gm ::
            ( EmbedG Module 'Id     cxt1
            , EmbedG Module 'Scalar cxt2
            ) => G cxt1 'Id t a -> G cxt2 'Scalar t a -> G Module 'Id t a

    runG (GM m) = runG m
    runG (Gm a1 a2) = runG a1'.*runG a2'
        where
            a1' = embedG @Module @'Id     a1
            a2' = embedG @Module @'Scalar a2

    mkG = GM . mkG

instance EmbedG Semigroup 'Id     Module where embedG (GM  a) = a
-- instance EmbedG Module    'Scalar Module where embedG a = unsafeCoerce a

-- instance Semigroup (G Module 'Id t a) where (+ ) e1 e2 = GM $ Gp e1 e2
-- instance (NestAT 'Scalar (NestAT 'Scalar t) ~ NestAT 'Scalar t) => Module    (G Module s t a) where (.*) e1 e2 = _ -- Gm e1 (reTag e2)
--
-- instance
--     ( Show (AppAT t a)
--     , Show (Scalar (AppAT t a))
--     , ValidScalar (Scalar (AppAT t a))
--     ) => Show (G Module t a)
--         where
--     show (GM a) = show a
--     show (Gm a1 a2) = "("++show a1'++".*"++show a2'++")"
--         where
--             a1' = embedG @Module @'Id     a1
--             a2' = embedG @Module @'Scalar a2

--------------------------------------------------------------------------------

instance (Show (AppAT t a), Num (AppAT t a)) => Num (F Semigroup t a)
    where fromInteger = unTag . Fi . fromInteger
instance (Show (AppAT t a), Num (AppAT t a)) => Num (F Module t a)
    where fromInteger = unTag . FM . fromInteger
-- instance (Show (AppAT t a), Num (AppAT t a)) => Num (F Hilbert t a)
--     where fromInteger = FH . fromInteger

type instance Scalar (F cxt t a) = F cxt (NestAT 'Scalar t) a

class FAlgebra (cxt::Type->Constraint) where
    data F cxt (t::AT) a
    runF :: cxt (AppAT t a) => F cxt (TagAT t' t) a -> AppAT (TagAT t' t) a
    mkF :: {-Show (AppAT t a) =>-} AppAT t a -> F cxt (TagAT 'Id t) a

--     laws :: [Law cxt t a]
--
-- data Law cxt t a = Law
--     { name :: String
--     , lhs :: F cxt t a
--     , rhs :: F cxt t a
--     }

class (FAlgebra cxt1, FAlgebra cxt2) => EmbedF cxt1 t cxt2 where
    embedF :: F cxt2 t' a -> F cxt1 (TagAT t t') a

instance FAlgebra cxt => EmbedF cxt 'Id cxt where
    embedF a = reTag a

-- instance Semigroup <: Module where
--     embedF = FM
--
-- instance Semigroup <: Hilbert where
--     embedF = FH . embedF
--
-- instance Module <: Hilbert where
--     embedF = FH

--------------------

instance FAlgebra Semigroup where
    data F Semigroup t a where
        Fi :: {-Show (AppAT t a) =>-} AppAT t a -> F Semigroup (TagAT 'Id t) a
        Fp ::
--             ( Show (F cxt t a)
            ( EmbedF Semigroup 'Id cxt
            ) => F cxt t a -> F cxt t a -> F Semigroup (TagAT 'Id t) a

    runF (Fi a) = a
    runF (Fp a1 a2) = runF a1' + runF a2'
        where
            a1' = embedF @Semigroup @'Id a1
            a2' = embedF @Semigroup @'Id a2

    mkF = Fi

instance Semigroup (F Semigroup t a) where (+) e1 e2 = unTag $ Fp e1 e2

instance Show (AppAT t a) => Show (F Semigroup t a) where
    show (Fi a) = show a
    show (Fp a1 a2) = "("++show a1'++"+"++show a2'++")"
        where
            a1' = embedF @Semigroup @'Id a1
            a2' = embedF @Semigroup @'Id a2

--------------------

instance FAlgebra Module where
    data F Module t a where
        FM  :: {-#UNPACK#-}!(F Semigroup (TagAT 'Id t) a) -> F Module (TagAT 'Id t) a
        Fm ::
--             ( FAlgebra cxt
--             , Show (F cxt t a)
--             , Show (F cxt ('TagAT 'Scalar t) a)
--             , Module (AppAT t a)
            ( EmbedF Module 'Id     cxt1
            , EmbedF Module 'Scalar cxt2
            ) => F cxt1 t a -> F cxt2 (TagAT 'Scalar t) a -> F Module (TagAT 'Id t) a

--     runF (FM m) = runF m
--     runF (Fm a1 a2) = runF a1'.*runF a2'
--         where
--             a1' = embedF @Module @'Id     a1
--             a2' = embedF @Module @'Scalar a2

    mkF = FM . mkF

instance EmbedF Semigroup 'Id     Module where embedF (FM  a) = reTag a
instance EmbedF Module    'Scalar Module where embedF a = unsafeCoerce a
-- instance EmbedF Module    'Scalar Module where embedF (FM a) = _reTag a

instance Semigroup (F Module t a) where (+ ) e1 e2 = unTag $ FM $ Fp e1 e2
instance (NestAT 'Scalar (NestAT 'Scalar t) ~ NestAT 'Scalar t) => Module    (F Module t a) where (.*) e1 e2 = unTag $     Fm e1 (reTag e2)

-- instance (Semigroup (AppAT t a)) => Semigroup (F Module t a) where (+ ) a1 a2 = FM $ Fp a1 a2
-- instance (Module    (AppAT t a)) => Module    (F Module t a) where (.*) a1 a2 =      Fm a1 (reTag a2)

instance
    ( Show (AppAT t a)
    , Show (Scalar (AppAT t a))
    , ValidScalar (Scalar (AppAT t a))
    ) => Show (F Module t a)
        where
    show (FM a) = show a
    show (Fm a1 a2) = "("++show a1'++".*"++show a2'++")"
        where
            a1' = embedF @Module @'Id     a1
            a2' = embedF @Module @'Scalar a2

--------------------

instance FAlgebra Hilbert where
    data F Hilbert t a where
        FH :: {-#UNPACK#-}!(F Module t a) -> F Hilbert t a
        Fd :: {-Hilbert (AppAT t a) =>-} F Hilbert t a -> F Hilbert t a -> F Hilbert (TagAT 'Scalar t) a

    runF (FH h) = runF h
--     runF (Fd a1 a2) = runF a1<>runF a2

--     mkF = FH . mkF
--
-- instance (Semigroup (AppAT t a)) => Semigroup (F Hilbert t a) where (+ ) a1 a2 = FH $ FM $ Fp a1 a2
-- instance (Module    (AppAT t a)) => Module    (F Hilbert t a) where (.*) a1 a2 = FH $      Fm a1 (reTag a2)
-- instance (Hilbert   (AppAT t a)) => Hilbert   (F Hilbert t a) where (<>) a1 a2 = unTag $   Fd a1 a2
--
-- instance Show (F Hilbert t a) where
--     show (FH a) = show a
--     show (Fd a1 a2) = "("++show a1++"<>"++show a2++")"

--------------------------------------------------------------------------------

instance (Show (AppAT t a), Num (AppAT t a)) => Num (B t a) where fromInteger = unTag . Bi . fromInteger

type instance Scalar (B t a) = B (NestAT 'Scalar t) a

data B (t::AT) a where
    Bi :: AppAT t a                      -> B (TagAT 'Id     t) a

    Bp :: B (TagAT 'Id t) a -> B (TagAT 'Id     t) a -> B (TagAT 'Id     t) a
    Bm :: B (TagAT 'Id t) a -> B (TagAT 'Scalar t) a -> B (TagAT 'Id     t) a
    Bd :: B (TagAT 'Id t) a -> B (TagAT 'Id     t) a -> B (TagAT 'Scalar t) a

instance Semigroup (B t a) where (+)  e1 e2 = unTag $ Bp (reTag e1) (reTag e2)
instance Module    (B t a) where (.*) e1 e2 = unTag $ Bm (reTag e1) (reTag e2)
instance Hilbert   (B t a) where (<>) e1 e2 = unTag $ Bd (reTag e1) (reTag e2)

goB :: Hilbert (AppAT t a) => B (TagAT t' t) a -> AppAT (TagAT t' t) a
goB (Bi a) = a
goB (Bp e1 e2) = goB e1+goB e2
goB (Bm e1 e2) = goB e1.*goB e2
goB (Bd e1 e2) = goB e1<>goB e2

instance
    ( Show (AppAT t a)
    ) => Show (B (TagAT t' t) a)
        where
    show (Bi e) = show e
    show (Bp e1 e2) = "("++show e1++"+"++show e2++")"
    show (Bm e1 e2) = "("++show e1++"*"++show e2++")"
    show (Bd e1 e2) = "("++show e1++"<>"++show e2++")"

--------------------------------------------------------------------------------

instance (Num a) => Num (C a b) where fromInteger = Ci . fromInteger

type instance Scalar (C a b) = C (Scalar a) b

data C a b where
    Ci :: a -> C a b
    Cp :: C a b -> C a b          -> C a b
    Cm :: C a b -> Scalar (C a b) -> C a b
--     Cm :: C a b -> C (Scalar a) b -> C a b
    Cd :: C a a -> C a a          -> C (Scalar a) a

instance Semigroup (C a b) where (+ ) = Cp
instance (Scalar (Scalar a)~(Scalar a)) => Module    (C a b) where (.*) = Cm
instance (Scalar (Scalar a)~(Scalar a)) => Hilbert   (C a a) where (<>) = Cd

goC :: (Module a, Hilbert b) => C a b -> a
goC (Ci a) = a
goC (Cp a1 a2) = goC a1+goC a2
-- goC (Cm a1 a2) = goC a1.*goC a2
goC (Cd a1 a2) = goC a1<>goC a2

instance (Show a, Show (Scalar a), Scalar (Scalar a)~Scalar a) => Show (C a b) where
    show (Ci a) = show a
    show (Cp e1 e2) = "("++show e1++"+"++show e2++")"
    show (Cm e1 e2) = "("++show e1++"*"++show e2++")"
--     show (Cd e1 e2) = "("++show e1++"<>"++show e2++")"

--------------------------------------------------------------------------------

-- instance (Show (AppAT t a), Num (AppAT t a)) => Num (D t a) where fromInteger = Di . fromInteger

type instance Scalar (D a b) = D a (Scalar b)

data D (t::AT) b where
    Di :: FixAT t a -> D t a

    Dp :: FixAT t a -> FixAT t a          -> D t a
    Dm :: FixAT t a -> Scalar (FixAT t a) -> D t a
    Dd :: FixAT t a -> FixAT t a          -> D (TagAT 'Scalar t) a

newtype Fix f e = Fix (f (Fix f e))
type D'  a b = Fix (D a) b

type family FixAT (t::AT) a where
    FixAT t (Fix (D t) a) = Fix (D t) a
    FixAT t a             = AppAT t a

type instance Scalar (Fix (D t) a) = Fix (D (NestAT 'Scalar t)) a

instance Semigroup (D' t a) where (+)  e1 e2 = Fix $ Dp e1 e2
-- instance Module    (D' t a) where (.*) e1 e2 = Fix $ Dm e1 e2
-- instance Hilbert   (D' (TagAT 'Scalar t) a) where (<>) e1 e2 = Fix $ Dd e1 e2

runD :: Hilbert (FixAT t a) => D t a -> FixAT t a
runD (Di a    ) = a
runD (Dp a1 a2) = a1+a2
runD (Dm a1 a2) = a1.*a2
-- runD (Dd a1 a2) = a1<>a2

--------------------------------------------------------------------------------

instance (Show (AppAT t a), Num (AppAT t a)) => Num (E t a) where fromInteger = Ei . fromInteger

type instance Scalar (E t a) = E (NestAT 'Scalar t) a

data E (t::AT) a where
    Ei :: Show      (AppAT t a) => AppAT t a                      -> E t a

    Ep :: Semigroup (AppAT t a) => E t a -> E t a                 -> E t a
    Em :: Module    (AppAT t a) => E t a -> E (TagAT 'Scalar t) a -> E t a
    Ed :: Hilbert   (AppAT t a) => E t a -> E t a                 -> E (TagAT 'Scalar t) a

instance Semigroup (AppAT t a) => Semigroup (E t a) where (+)  e1 e2 = Ep e1 e2
-- instance Module    (AppAT t a) => Module    (E t a) where (.*) e1 e2 = Em e1 (reTag e2)
-- instance Hilbert   (AppAT t a) => Hilbert   (E t a) where (<>) e1 e2 = unTag (Ed e1 e2)

instance
    ( Module (AppAT t a)
    , AppAT (NestAT 'Scalar t) a~Scalar (AppAT t a)
    , Scalar (Scalar (AppAT t a))~Scalar (AppAT t a)
    , NestAT 'Scalar (NestAT 'Scalar t) ~ NestAT 'Scalar t
    ) => Module    (E t a)
    where (.*) e1 e2 = Em e1 (reTag e2)

instance
    ( Hilbert (AppAT t a)
    , AppAT (NestAT 'Scalar t) a~Scalar (AppAT t a)
    , Scalar (Scalar (AppAT t a))~Scalar (AppAT t a)
    , NestAT 'Scalar (NestAT 'Scalar t) ~ NestAT 'Scalar t
    ) => Hilbert   (E t a)
    where (<>) e1 e2 = unTag (Ed e1 e2)

go :: E t a -> AppAT t a
go (Ei a) = a
go (Ep e1 e2) = go e1+go e2
go (Em e1 e2) = go e1.*go e2
go (Ed e1 e2) = go e1<>go e2

instance Show (E t a) where
    show (Ei e) = show e
    show (Ep e1 e2) = "("++show e1++"+"++show e2++")"
    show (Em e1 e2) = "("++show e1++"*"++show e2++")"
    show (Ed e1 e2) = "("++show e1++"<>"++show e2++")"

--------------------------------------------------------------------------------

data AT
    = Id
    | Scalar
    | TagAT AT AT

type family AppAT (t::AT) (a::Type) :: Type
type instance AppAT 'Id a = a
type instance AppAT 'Scalar a = Scalar a
type instance AppAT (TagAT t t') a = AppAT t (AppAT t' a)

type family NestAT (t::AT) (a::AT) :: AT
type instance NestAT t       'Id     = t
type instance NestAT 'Id     t       = t
type instance NestAT 'Scalar 'Scalar = 'Scalar
type instance NestAT 'Scalar (TagAT 'Scalar t) = (TagAT 'Scalar t)
type instance NestAT t1      (TagAT 'Id     t) = (TagAT t1 t)

--------------------------------------------------------------------------------

type instance Scalar Integer = Integer
instance Semigroup Integer where (+) = (P.+)
instance Module Integer where (.*) = (P.*)
instance Hilbert Integer where (<>) = (P.*)

type instance Scalar Int = Int
instance Semigroup Int where (+) = (P.+)
instance Module Int where (.*) = (P.*)
instance Hilbert Int where (<>) = (P.*)

type instance Scalar (a,b) = Scalar b
instance (Semigroup a,Semigroup b) => Semigroup (a,b) where
    (a1,b1)+(a2,b2) =(a1+a2,b1+b2)
instance (Module a, Module b, Scalar a~Scalar b) => Module (a,b) where
    (a1,b1).*r =(a1.*r,b1.*r)
instance (Hilbert a, Hilbert b, Scalar a~Scalar b, ValidScalar b) => Hilbert (a,b) where
    (a1,b1)<>(a2,b2) =(a1<>a2)+(b1<>b2)

instance (Num a, Num b) => Num (Int,Int) where
    fromInteger i = (fromInteger i, fromInteger i)
