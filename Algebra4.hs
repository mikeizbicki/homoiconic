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

-------------------------------------------------------------------------------

type IsScalar a = (Scalar a~a, Module a)
type ValidScalar a = IsScalar (Scalar a)

class Semigroup a where
    (+) :: a -> a -> a

class (ValidScalar a, Semigroup a) => Module a where
    (.*) :: a -> Scalar a -> a

class (ValidScalar a, Module a) => Hilbert a where
    (<>) :: a -> a -> Scalar a

--------------------

data E (t::AT) a where
    Ep :: Semigroup (AppAT t a) => E t a -> E t a                 -> E t a
    Em :: Module    (AppAT t a) => E t a -> E (AppAT 'Scalar t) a -> E t a
    Ed :: Hilbert   (AppAT t a) => E t a -> E r a                 -> E (AppAT 'Scalar t) a

instance Semigroup (AppAT t a) => Semigroup (E t a) where (+) = Ep

instance
    ( Module (AppAT t a)
    , ValidScalar (E t a)
    ) => Module (E t a)
    where (.*) = Em

instance
    ( Hilbert (AppAT t a)
    , ValidScalar (E t a)
    ) => Hilbert (E t a)
    where (<>) = Ed

type instance Scalar (E t a) = E (AppAT 'Scalar t) a

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

--------------------------------------------------------------------------------

data AT
    = Id
    | Scalar
    | TagAT AT AT

type family AppAT (t::AT) (a::k) :: k
type instance AppAT 'Id a = a
type instance AppAT 'Scalar a = Scalar a
type instance AppAT (TagAT t t') a = AppAT t (AppAT t' a)

----------------------------------------

data Expr (t::AT) a where
    Expr_plus :: Semigroup (AppAT t a)  => Expr t a -> Expr t a                     -> Expr t a
--     Expr_mul  ::
--         ( Module (AppAT t a)
--         ) => Expr t a -> Expr (TagAT 'Scalar t) a     -> Expr t a
    Expr_mul  :: Module (AppAT t a)     => Expr t a -> Expr (TagAT 'Scalar t) a     -> Expr t a
--     Expr_mul  :: Module (AppAT t a)     => Expr t a -> Expr t (Scalar a)            -> Expr t a
--     Expr_dp   :: Hilbert (AppAT t a)    => Expr t a -> Expr t a                     -> Expr (TagAT 'Scalar t) a

    Expr_Id   :: AppAT t a          -> Expr t a

mkExpr = Expr_Id

type instance Scalar (Expr t a) = Expr (AppAT 'Scalar t) a
-- type instance Scalar (Expr t a) = Expr t (Scalar a)

--------------------

instance Semigroup (AppAT t a) => Semigroup (Expr t a) where
    (+) = Expr_plus

instance (ValidScalar (Expr t a), Module (AppAT t a)) => Module (Expr t a) where
--     (.*) = Expr_mul

-- instance (ValidScalar (AppAT t a), Hilbert (AppAT t a)) => Hilbert (Expr t a) where
--     (<>) = Expr_dp

----------------------------------------

go :: Expr t a -> AppAT t a
go (Expr_Id a) = a
go (Expr_plus e1 e2) = go e1+go e2
go (Expr_mul  e1 e2) = go e1.*go e2
-- go (Expr_dp   e1 e2) = go e1<>go e2

----------------------------------------

instance
    ( Show (AppAT t a)
    , Show (Scalar (AppAT t a))
    , Scalar (Scalar (AppAT t a))~Scalar (AppAT t a)
    ) => Show (Expr t a)
        where
    show (Expr_Id a)       = show a
    show (Expr_plus e1 e2) = "("++show e1++"+" ++show e2++")"
    show (Expr_mul  e1 e2) = "("++show e1++".*"++show e2++")"

instance {-#overlaps#-}
    ( Show (Scalar (AppAT t a))
    , Show (AppAT t a)
    , Scalar (Scalar (AppAT t a))~Scalar (AppAT t a)
    ) => Show (Expr (TagAT 'Scalar t) a)
        where
    show (Expr_Id a)       = show a
    show (Expr_plus e1 e2) = "("++show e1++"+" ++show e2++")"
    show (Expr_mul  e1 e2) = "("++show e1++".*"++show e2++")"
--     show (Expr_dp   e1 e2) = "("++show e1++"<>"++show e2++")"

instance Num (AppAT t a) => Num (Expr t a) where
    fromInteger = Expr_Id . fromInteger
