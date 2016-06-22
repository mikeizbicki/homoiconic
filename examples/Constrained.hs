-- these options are required for the class hierarchy to be valid
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}

{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}

-- these options are required for constrained FAlgebras
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

import Prelude hiding (Monoid (..),(-),(+),negate,(==),minBound,fromInteger,elem)
import qualified Prelude as P

import Homoiconic.Constrained

--------------------------------------------------------------------------------

class Topology a => Poset a where
    inf :: a -> a -> a

    (<=) :: a -> a -> Logic a
    (<=) a1 a2 = inf a1 a2 == a1

    compare :: a -> a -> Maybe Ordering

#define mkPoset(x) \
instance Poset x where inf = P.min

mkPoset(Float)
mkPoset(Double)
mkPoset(Rational)
mkPoset(Integer)
mkPoset(Int)
mkPoset(Bool)
mkPoset(Char)

instance Poset () where
    inf () () = ()

instance (Poset a, Poset b) => Poset (a,b) where
    inf (a1,b1) (a2,b2) = (inf a1 a2, inf b1 b2)

----------------------------------------

class Poset a => LowerBounded a where
    minBound :: a

#define mkLowerBounded(x) \
instance LowerBounded x where minBound = P.minBound

mkLowerBounded(Bool)
mkLowerBounded(Char)

instance LowerBounded () where
    minBound = ()

instance (LowerBounded a, LowerBounded b) => LowerBounded (a,b) where
    minBound = (minBound,minBound)

----------------------------------------

class Semigroup a => Container a where
    type Elem a
    elem :: Elem a -> a -> Logic a
    cons :: Elem a -> a -> a
    snoc :: a -> Elem a -> a
    fromList1 :: Elem a -> [Elem a] -> a
    fromList1N :: Int -> Elem a -> [Elem a] -> a

instance Container Bool where
    type Elem Bool = ()
    elem _ True = True
    elem _ False = False

instance Container () where
    type Elem () = ()
    elem () () = ()

instance (Container a, Container b) => Container (a,b) where
    type Elem (a,b) = (Elem a, Elem b)
    elem (ea,eb) (a,b) = (elem ea a, elem eb b)

----------------------------------------

class (Container a, LowerBounded (Elem a), IfThenElse (Logic a)) => IfThenElse a where
    ifThenElse :: a -> b -> b -> b
    ifThenElse a b1 b2 = ifThenElse (minBound `elem` a) b1 b2

instance IfThenElse Bool where
    ifThenElse True  b _ = b
    ifThenElse False _ b = b

instance IfThenElse () where
    ifThenElse () b _ = b

--------------------

newtype NonNegative a = NonNegative a
    deriving Show

instance (Monoid a, Poset a, Num a) => Topology (NonNegative a) where
    type Logic (NonNegative a) = NonNegative a
    (==) (NonNegative a1) (NonNegative a2) = NonNegative (abs $ a1 P.- a2)

instance (Monoid a, Poset a, Num a) => Poset (NonNegative a) where
    inf (NonNegative a1) (NonNegative a2) = NonNegative (inf a1 a2)

instance (Monoid a, Poset a, Num a) => LowerBounded (NonNegative a) where
    minBound = NonNegative zero

instance (Monoid a, Poset a, Num a) => Semigroup (NonNegative a) where
    (NonNegative a1)+(NonNegative a2) = NonNegative (a1+a2)

instance (Monoid a, Poset a, Num a) => Container (NonNegative a) where
    type Elem (NonNegative a) = NonNegative a
    elem (NonNegative a1) (NonNegative a2) = NonNegative (a1 P.- a2)

----------------------------------------

type IdempLogic a = Logic (Logic (Logic a)) ~ Logic (Logic a)

class (Container (Logic a), IdempLogic a) => Topology a where
    type Logic a
    (==) :: a -> a -> Logic a

#define mkTopology(x) \
instance Topology x where \
    type Logic x = Bool; \
    (==) = (P.==)
-- type instance Logic x = Bool; \

mkTopology(Float)
mkTopology(Double)
mkTopology(Rational)
mkTopology(Integer)
mkTopology(Int)
mkTopology(Bool)
mkTopology(Char)

instance Topology () where
    type Logic () = ()
    (==) () () = ()

-- type instance Logic (a,b) = (Logic a, Logic b)
instance (Topology a, Topology b) => Topology (a,b) where
    type Logic (a,b) = (Logic a, Logic b)
    (==) (a1,b1) (a2,b2) = (a1==a2,b1==b2)

----------------------------------------

class Topology a => Semigroup a where
    (+) :: a -> a -> a

instance Semigroup Int where (+) = (P.+)

instance Semigroup () where
    ()+() = ()

instance (Semigroup a, Semigroup b) => Semigroup (a,b) where
    (a1,b1)+(a2,b2) = (a1+a2,b1+b2)

----------------------------------------

class Semigroup a => Monoid a where
    zero :: a
    fromInteger :: Int -> a

instance Monoid Int where zero = 0

instance Monoid () where
    zero = ()

instance (Monoid a, Monoid b) => Monoid (a,b) where
    zero=(zero,zero)

----------------------------------------

type family Scalar a
type ValidScalar a = (Module (Scalar a), Scalar (Scalar a)~Scalar a)

class (Monoid a, ValidScalar a) => Module a where
--     type Scalar a
    (.*) :: Scalar a -> a -> a


type instance Scalar Int = Int
instance Module Int where
--     type Scalar Int = Int
    (.*) = (P.*)

type instance Scalar () = ()
instance Module () where
--     type Scalar () = ()
    ().*() = ()

type instance Scalar (a,b) = Scalar b
instance (Module a, Module a) => Module (a,a) where
--     type Scalar (a,a) = Scalar a
    s.*(a1,b1) = (s.*a1,s.*b1)

----------------------------------------

class Module a => Hilbert a where
    (<>) :: a -> a -> Scalar a

instance Hilbert Int where (<>) = (P.*)

instance Hilbert () where
    ()<>()=()

instance (Semigroup (Scalar a), Hilbert a) => Hilbert (a,a) where
    (a1,b1)<>(a2,b2) = (a1<>a2) + (b1<>b2)

----------------------------------------

class Hilbert a => Tensorable a where
    type Tensor a
    floo :: a -> a -> Tensor a

instance Tensorable Int where
    type Tensor Int = Int

instance Tensorable () where
    type Tensor () = ()

instance (Semigroup (Scalar a), Hilbert a, Tensorable a) => Tensorable (a,a) where
    type Tensor (a,a) = ((a,a),(a,a))

--------------------------------------------------------------------------------

type instance Scalar Bool = Bool
instance Semigroup Bool
instance Monoid Bool
instance Module Bool where
--     type Scalar Bool = Bool
instance Hilbert Bool
instance Tensorable Bool where
    type Tensor Bool = Bool

--------------------------------------------------------------------------------

mkTagFromCnst ''Scalar [t| forall a. ValidScalar a |]
mkFAlgebra ''Tensorable
mkFAlgebra ''Container
-- mkFAlgebra ''IfThenElse

type instance FreeConstraints t a
    = ( AppTags (ConsTag TScalar t) a
      ~ Scalar (AppTags t a)
      , AppTags (ConsTag TScalar (ConsTag TLogic (ConsTag TLogic t))) a
      ~ Scalar (AppTags (ConsTag_TLogic (ConsTag_TLogic t)) a)
      )

--------------------------------------------------------------------------------

main = do
    let x = Pure (1,2) :: AST Tensorable '[]        (Int,Int)
        y = Pure 2     :: AST Tensorable '[TScalar] (Int,Int)

--     let expr1 = ((x+x)==x) `inf` minBound
--     putStrLn $ "expr1 = "++show expr1
--     putStrLn $ "runAST expr1 = "++show (runAST expr1)

--     let expr2 = (y.*y.*y.*x) + x
--     putStrLn $ "expr2 = "++show expr2
--     putStrLn $ "runAST expr2 = "++show (runAST expr2)

    putStrLn "done."
