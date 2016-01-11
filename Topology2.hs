{-# LANGUAGE UndecidableSuperClasses #-}

module Topology
    where

import qualified Prelude as P
import LocalPrelude
import Lattice

----------------------------------------

type Logic a = Community (Neighborhood a) -> Bool

data Community a where
    NNil    :: Community a
    NCons   :: Poset a => a -> Community (Neighborhood a) -> Community a
    NBranch :: Community a -> Community b -> Community (a,b)

instance Poset (Community a) where
    inf NNil _ = NNil
    inf _ NNil = NNil
    inf (NCons na1 c1) (NCons na2 c2) = NCons (inf na1 na2) (inf c1 c2)
    inf (NBranch a1 b1) (NBranch a2 b2) = NBranch (inf a1 a2) (inf b1 b2)

instance LowerBounded (Community a) where
    lowerBound = NNil

mkTuple :: LowerBounded a => Community a -> (a, Community (Neighborhood a))
mkTuple NNil          = (lowerBound,NNil)
mkTuple (NCons a cna) = (a,cna)
-- mkTuple (NBranch a b) = ((na,nb),NBranch ca cb)
--     where
--         (na,ca) = mkTuple a
--         (nb,cb) = mkTuple b

--------------------

class
    ( Topology (Neighborhood a)
    , LowerBounded (Neighborhood a)
    ) => Topology a
        where

    type Neighborhood a
    isNeighbor :: a -> a -> Logic a

    infixr 4 ==
    (==) :: a -> a -> Logic a
    (==) a1 a2 = isNeighbor a1 a2 || isNeighbor a2 a1

    infixr 4 /=
    (/=) :: a -> a -> Logic a
    (/=) = not (==)

    infixr 4 <=
    (<=) :: Poset a => a -> a -> Logic a
    (<=) a1 a2 = inf a1 a2 == a1

    infixr 4 <
    (<) :: Poset a => a -> a -> Logic a
    (<) a1 a2 = inf a1 a2 == a1 && a1 /= a2

    infixr 4 >=
    (>=) :: Lattice a => a -> a -> Logic a
    (>=) a1 a2 = sup a1 a2 == a1

    infixr 4 >
    (>) :: Lattice a => a -> a -> Logic a
    (>) a1 a2 = sup a1 a2 == a1 && a1 /= a2

--------------------

type OpenSet x = (x, Neighborhood x)

newtype Borel x = Borel [OpenSet x]

-- NOTE: Borel sets can't be represented using this system
-- because we can't take the intersection of two open sets

----------------------------------------

instance Topology Float where
    type Neighborhood Float = Discrete (NonNegative Rational)
    isNeighbor a1 a2 NNil = a1 P.== a2
    isNeighbor a1 a2 (r `NCons` n) = ((Discrete $ NonNegative $ toRational $ P.abs $ a1 P.- a2) <= r) n

instance Topology Rational where
    type Neighborhood Rational = Discrete (NonNegative Rational)
    isNeighbor a1 a2 (Discrete (NonNegative r) `NCons` n) = ((P.abs $ a1 P.- a2) P.<= r)

instance Topology Integer where
    type Neighborhood Integer = Discrete (NonNegative Integer)
    isNeighbor a1 a2 (Discrete (NonNegative i) `NCons` n) = ((P.abs $ a1 P.- a2) P.<= i)

instance Topology a => Topology (Discrete a) where
    type Neighborhood (Discrete a) = ()
    isNeighbor (Discrete a1) (Discrete a2) _ = isNeighbor a1 a2 lowerBound

instance Topology a => Topology (NonNegative a) where
    type Neighborhood (NonNegative a) = Neighborhood a
    isNeighbor (NonNegative a1) (NonNegative a2) = isNeighbor a1 a2

--------------------

instance Topology a => Topology [a] where
    type Neighborhood [a] = Neighborhood a
    (==) (x:xs) (y:ys) = x==y && xs==ys
    (==) []     []     = upperBound
    (==) _      _      = lowerBound

instance Topology a => Poset [a] where
    inf xs ys = go xs ys []
        where
            go :: [a] -> [a] -> [a] -> [a]
            go (x:xs) (y:ys) ret = if x==y
                then go xs ys (ret++[x])
                else ret
            go _ _ ret = ret

instance Topology a => LowerBounded [a] where
    lowerBound = []

--------------------


instance (Topology a, Topology b) => Topology (a -> b) where
    type Neighborhood (a -> b) = ([a], Neighborhood b)
    (==) f g (NBranch (NCons xs _) nb) = go xs
                where
                    go (x:xs) = (f x==g x) nb && go xs
                    go []     = True

instance (Topology a, Topology b) => Topology (a,b) where
    type Neighborhood (a,b) = (Neighborhood a, Neighborhood b)
    (==) (a1,b1) (a2,b2) NNil            = (a1==a2) NNil && (b1==b2) NNil
    (==) (a1,b1) (a2,b2) (NBranch ea eb) = (a1==a2) ea   && (b1==b2) eb

instance Topology () where
    type Neighborhood () = ()
    (==) _ _ = \_ -> True

----------------------------------------

class (Topology (Scalar a), Num (Scalar a), Lattice (Scalar a)) => Metric a where
    type Scalar a
    distance :: a -> a -> Scalar a

instance Metric Float where
    type Scalar Float = Float
    distance a1 a2 = P.abs $ a1 P.- a2

-- We want every Metric space to be an instance of a topology,
-- but this newtype doesn't ensure that
newtype TopMet a = TopMet a

instance Metric a => Topology (TopMet a) where
    type Neighborhood (TopMet a) = Discrete (NonNegative (Scalar a))
    isNeighbor (TopMet a1) (TopMet a2) (n1 `NCons` n2) = ((Discrete $ NonNegative $ distance a1 a2) <= n1) n2

----------------------------------------

ifThenElse :: LowerBounded a => (a -> Bool) -> b -> b -> b
ifThenElse f a1 a2 = case f lowerBound of
    True -> a1
    False -> a2

instance Show (Community a -> Bool) where
    show f = show $ f lowerBound

