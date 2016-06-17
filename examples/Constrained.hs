-- these options are required for the class hierarchy to be valid
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}

-- these options are required for constrained FAlgebras
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

import Prelude hiding (Monoid (..),(-),(+),negate,(==),minBound,fromInteger)
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

instance (Poset a, Poset b) => Poset (a,b) where
    inf (a1,b1) (a2,b2) = (inf a1 a2, inf b1 b2)

----------------------------------------

class Poset a => LowerBounded a where
    minBound :: a

#define mkLowerBounded(x) \
instance LowerBounded x where minBound = P.minBound

mkLowerBounded(Bool)
mkLowerBounded(Char)

instance (LowerBounded a, LowerBounded b) => LowerBounded (a,b) where
    minBound = (minBound,minBound)

----------------------------------------

-- type ValidLogic a = Logic (Logic (Logic a)) ~ Logic (Logic a)

class (LowerBounded (Logic a), Logic (Logic (Logic a))~Logic (Logic a)) => Topology a where
    type Logic a
    (==) :: a -> a -> Logic a

#define mkTopology(x) \
instance Topology x where \
    type Logic x = Bool; \
    (==) = (P.==)

mkTopology(Float)
mkTopology(Double)
mkTopology(Rational)
mkTopology(Integer)
mkTopology(Int)
mkTopology(Bool)
mkTopology(Char)

instance (Topology a, Topology b) => Topology (a,b) where
    type Logic (a,b) = (Logic a, Logic b)
    (==) (a1,b1) (a2,b2) = (a1==a2,b1==b2)

----------------------------------------

class Topology a => Semigroup a where
    (+) :: a -> a -> a

instance Semigroup Int where (+) = (P.+)
instance (Semigroup a, Semigroup b) => Semigroup (a,b) where
    (a1,b1)+(a2,b2) = (a1+a2,b1+b2)

----------------------------------------

class Semigroup a => Monoid a where
    zero :: a
    fromInteger :: Int -> a

instance Monoid Int where zero = 0
instance (Monoid a, Monoid b) => Monoid (a,b) where
    zero=(zero,zero)

----------------------------------------

class (Monoid a, Module (Scalar a), Scalar (Scalar a)~Scalar a) => Module a where
    type Scalar a
    (.*) :: Scalar a -> a -> a

-- type instance Scalar Bool = Bool
instance Semigroup Bool
instance Monoid Bool
instance Module Bool where
    type Scalar Bool = Bool

-- type instance Scalar Int = Int
-- type instance Scalar (a,b) = Scalar b

instance Module Int where
    type Scalar Int = Int
    (.*) = (P.*)

instance (Module a, Module a) => Module (a,a) where
    type Scalar (a,a) = Scalar a
    s.*(a1,b1) = (s.*a1,s.*b1)

----------------------------------------

class Module a => Hilbert a where
    (<>) :: a -> a -> Scalar a

instance Hilbert Int where (<>) = (P.*)
instance (Semigroup (Scalar a), Hilbert a) => Hilbert (a,a) where
    (a1,b1)<>(a2,b2) = (a1<>a2) + (b1<>b2)

----------------------------------------

instance Hilbert Bool
instance Floobert Bool where
    type Floo Bool = Bool

class (Hilbert a, Hilbert (Floo a)) => Floobert a where
    type Floo a
    floo :: Floo a -> a

instance Floobert Int where
    type Floo Int = Int
instance (Semigroup (Scalar a), Hilbert a, Floobert a) => Floobert (a,a) where
    type Floo (a,a) = a

--------------------------------------------------------------------------------

mkFAlgebra ''Floobert

type instance FreeConstraints t a
    = ( AppTags (ConsTag TScalar t) a
      ~ Scalar (AppTags t a)
      , AppTags (ConsTag TScalar (ConsTag TLogic (ConsTag TLogic t))) a
      ~ Scalar (AppTags (ConsTag_TLogic (ConsTag_TLogic t)) a)
      )

--------------------------------------------------------------------------------

main = do
    let x = Pure (1,2) :: AST Floobert '[]        (Int,Int)
        y = Pure 2     :: AST Floobert '[TScalar] (Int,Int)

    let expr1 = ((x+x)==x) `inf` minBound
    putStrLn $ "expr1 = "++show expr1
    putStrLn $ "runAST expr1 = "++show (runAST expr1)

    let expr2 = (y.*y.*y.*x) + x
    putStrLn $ "expr2 = "++show expr2
    putStrLn $ "runAST expr2 = "++show (runAST expr2)

    putStrLn "done."
