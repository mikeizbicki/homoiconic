{-# LANGUAGE UndecidableSuperClasses #-}

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
import GHC.Generics

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

instance (Show (AppAT t a), Num (AppAT t a)) => Num (F Semigroup t a)
    where fromInteger = Fi . fromInteger
instance (Show (AppAT t a), Num (AppAT t a)) => Num (F Module t a)
    where fromInteger = FM . fromInteger
instance (Show (AppAT t a), Num (AppAT t a)) => Num (F Hilbert t a)
    where fromInteger = FH . fromInteger

type instance Scalar (F cxt t a) = F cxt (NestAT 'Scalar t) a

class FAlgebra (cxt::Type->Constraint) where
    data F cxt (t::AT) a
    runF :: F cxt t a -> AppAT t a
    mkF :: Show (AppAT t a) => AppAT t a -> F cxt t a

--------------------

instance FAlgebra Semigroup where
    data F Semigroup t a where
        Fi :: Show (AppAT t a) => AppAT t a -> F Semigroup t a
        Fp ::
            ( Show (F cxt t a)
            , FAlgebra cxt
            , Semigroup (AppAT t a)
            ) => F cxt t a -> F cxt t a -> F Semigroup t a
    runF (Fi a) = a
    runF (Fp a1 a2) = runF a1+runF a2
    mkF = Fi

instance (Semigroup (AppAT t a)) => Semigroup (F Semigroup t a) where (+) e1 e2 = Fp e1 e2

instance Show (F Semigroup t a) where
    show (Fi a) = show a
    show (Fp a1 a2) = "("++show a1++"+"++show a2++")"

--------------------

instance FAlgebra Module where
    data F Module t a where
        FM :: {-#UNPACK#-}!(F Semigroup t a) -> F Module t a
        Fm ::
            ( FAlgebra cxt
            , Show (F cxt t a)
            , Show (F cxt ('TagAT 'Scalar t) a)
            , Module (AppAT t a)
            ) => F cxt t a -> F cxt (TagAT 'Scalar t) a -> F Module t a
    runF (FM m) = runF m
    runF (Fm a1 a2) = runF a1.*runF a2
    mkF = FM . mkF

instance (Semigroup (AppAT t a)) => Semigroup (F Module t a) where (+ ) a1 a2 = FM $ Fp a1 a2
instance (Module    (AppAT t a)) => Module    (F Module t a) where (.*) a1 a2 =      Fm a1 (reTag a2)

instance Show (F Module t a) where
    show (FM a) = show a
    show (Fm a1 a2) = "("++show a1++".*"++show a2++")"

--------------------

instance FAlgebra Hilbert where
    data F Hilbert t a where
        FH :: {-#UNPACK#-}!(F Module t a) -> F Hilbert t a
        Fd :: Hilbert (AppAT t a) => F Hilbert t a -> F Hilbert t a -> F Hilbert (TagAT 'Scalar t) a
    runF (FH h) = runF h
    runF (Fd a1 a2) = runF a1<>runF a2
    mkF = FH . mkF

instance (Semigroup (AppAT t a)) => Semigroup (F Hilbert t a) where (+ ) a1 a2 = FH $ FM $ Fp a1 a2
instance (Module    (AppAT t a)) => Module    (F Hilbert t a) where (.*) a1 a2 = FH $      Fm a1 (reTag a2)
instance (Hilbert   (AppAT t a)) => Hilbert   (F Hilbert t a) where (<>) a1 a2 = unTag $   Fd a1 a2

instance Show (F Hilbert t a) where
    show (FH a) = show a
    show (Fd a1 a2) = "("++show a1++"<>"++show a2++")"

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
type instance NestAT 'Scalar 'Scalar = 'Scalar

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

