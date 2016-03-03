-- {-# LANGUAGE UndecidableSuperClasses #-}
-- {-# LANGUAGE TypeApplications #-}
module Topology1
    where

import Prelude (fromInteger)
import qualified Prelude as P
import LocalPrelude
import Lattice

import Debug.Trace

--------------------------------------------------------------------------------

type Community a = Neighborhood a
type Logic a = Neighborhood a -> Bool

ifThenElse :: LowerBounded b => (b -> Bool) -> a -> a -> a
ifThenElse f a1 a2 = case f lowerBound of
    True  -> a1
    False -> a2

----------------------------------------

class
--     ( Topology (Neighborhood a)
    ( LowerBounded (Neighborhood a)
    , Lattice (Neighborhood a)
    ) => Topology a
        where

    type Neighborhood a

    {-# MINIMAL isNeighbor | (==) #-}

    isNeighbor :: a -> (a,Neighborhood a) -> Bool
    isNeighbor a1 (a2,n) = (a1==a2) n

    infixr 4 ==
    (==) :: a -> a -> Logic a
    (==) a1 a2 n = isNeighbor a1 (a2,n)

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

-- NOTE:
-- This law states that (==) is a Lattice and LowerBound homomorphism from (Neighborhood a) to Bool.
-- This seems like the right level of strictness because these are the superclasses of Topology.
law_Topology_inf :: Topology a => a -> a -> Neighborhood a -> Neighborhood a -> Logic Bool
law_Topology_inf a1 a2 c1 c2 = (f (c1&&c2) == (f c1 && f c2))
                            && (f (c1||c2) == (f c1 || f c2))
                            && (lowerBound == f lowerBound)
    where
        f = (a1==a2)

--------------------

-- | Technically, this class corresponds to the idea of a "fiber bundle."
-- A Manifold is a fiber bundle where Neighborhood is a Euclidean space.
-- Because of our "approximate laws" induced by the topology, however,
-- we don't need to introduce a separate type class for the two ideas.
-- I'm not yet sure if this is good or just confusing.
--
-- TODO:
-- Is it possible to construct "free" manifolds from semigroups or lattices?
class Topology a => Manifold a where
    getNeighbor :: a -> Neighborhood a -> a

    getNeighborhood :: a -> a -> Neighborhood a

law_Manifold_edge :: Manifold a => a -> Neighborhood a -> Neighborhood a -> Bool -- Logic a
law_Manifold_edge a n1 n2 = isNeighbor a (a', n1') && not (isNeighbor a (a', n2'))
    where
        n1' = inf n1 n2
        n2' = sup n1 n2
        a'  = getNeighbor a n1'

-- law_getNeighborhood :: Manifold a => a -> a -> Logic a
-- law_getNeighborhood a1 a2 = getNeighbor a1 (getNeighborhood a1 a2) == a2
law_getNeighborhood :: (Topology (Neighborhood a), Manifold a) => a -> Neighborhood a -> Logic (Neighborhood a)
law_getNeighborhood a1 n1 = getNeighborhood a1 (getNeighbor a1 n1) == n1

----------------------------------------

instance (Topology a, Topology b) => Topology (a -> b) where
    type Neighborhood (a -> b) = ([a], Neighborhood b)
    (==) f g (xs,nb) = go xs
                where
                    go (x:xs) = (f x==g x) nb && go xs
                    go []     = True

instance (Topology a, Topology b) => Topology (a,b) where
    type Neighborhood (a,b) = (Neighborhood a, Neighborhood b)
    (==) (a1,b1) (a2,b2) = \(ea,eb) -> (a1==a2) ea && (b1==b2) eb

instance Topology () where
    type Neighborhood () = ()
    (==) _ _ = \_ -> True

instance Topology Int where
    type Neighborhood Int = ()
    (==) a1 a2 = \_ -> a1 P.== a2

instance Topology Integer where
    type Neighborhood Integer = ()
    (==) a1 a2 = \_ -> a1 P.== a2

instance Topology Bool where
    type Neighborhood Bool = ()
    (==) a1 a2 = \_ -> a1 P.== a2

instance Topology Char where
    type Neighborhood Char = ()
    (==) a1 a2 = \_ -> a1 P.== a2

instance Topology a => Topology (Discrete a) where
    type Neighborhood (Discrete a) = ()
    (==) (Discrete a1) (Discrete a2) _ = (a1==a2) lowerBound

instance Topology Float where
    type Neighborhood Float = Discrete (NonNegative Rational)
    isNeighbor a1 (a2,Discrete (NonNegative n)) = (toRational (P.abs (a1 P.- a2)) <= n) (Discrete $ NonNegative 0)

instance Topology Double where
    type Neighborhood Double = Discrete (NonNegative Rational)
    isNeighbor a1 (a2,Discrete (NonNegative n)) = (toRational (P.abs (a1 P.- a2)) <= n) (Discrete $ NonNegative 0)

instance Topology Rational where
    type Neighborhood Rational = Discrete (NonNegative Rational)
    isNeighbor a1 (a2,Discrete (NonNegative n)) = P.abs (a1 P.- a2) P.<= n

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

instance Topology a => Lattice [a] where
    sup xs ys = xs ++ ys

--------------------------------------------------------------------------------

-- | Category of topological spaces.
-- The morphisms are continuous functions.
--
-- See <wikipedia https://en.wikipedia.org/wiki/Category_of_topological_spaces>
-- for more details.
data Top a b where
    Top :: (Topology a, Topology b) =>
        { arrow :: a -> b
        , inv :: a -> Neighborhood b -> Neighborhood a
        }
        -> Top a b

comp :: forall a b c. Top b c -> Top a b -> Top a c
comp (Top f1 inv1) (Top f2 inv2) = Top
    { arrow = f1 . f2
    , inv = \a nc -> inv2 a (inv1 (f2 a) nc)
    }

prop_Top :: Top a b -> a -> Neighborhood b -> (a -> Bool)
prop_Top (Top f inv) a nb =
    \a2 -> (a2 `isNeighbor` (a,inv a nb)) ==> (f a2 `isNeighbor` (f a, nb))

instance (Topology a, Topology b) => Topology (Top a b) where
    type Neighborhood (Top a b) = Neighborhood (a -> b)
    (==) (Top f _) (Top g _) = f==g

--------------------------------------------------------------------------------

class (Poset (Scalar a), Topology a) => Metric a where
    type Scalar a
    distance :: a -> a -> Scalar a

orderTopology_isNeighbor ::
    ( Neighborhood a~NonNegative a
    , a~Scalar a
    , Metric a
    ) => a -> (a,Neighborhood a) -> Bool
orderTopology_isNeighbor a1 (a2,NonNegative na) = (distance a1 a2 <= na) lowerBound

