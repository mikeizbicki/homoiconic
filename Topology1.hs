{-# LANGUAGE UndecidableSuperClasses #-}
module Topology1
    where

import qualified Prelude as P
import LocalPrelude
import Lattice

--------------------------------------------------------------------------------

type Logic a = Neighborhood a -> Bool

ifThenElse :: LowerBounded b => (b -> Bool) -> a -> a -> a
ifThenElse f a1 a2 = case f lowerBound of
    True  -> a2
    False -> a1

----------------------------------------

-- class LowerBounded (Neighborhood a) => Topology a where
class (Topology (Neighborhood a), LowerBounded (Neighborhood a), Lattice (Neighborhood a)) => Topology a where
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

law_Topology_equality :: Topology a => a -> Logic a
law_Topology_equality a = a==a

-- law_Topology_compatibility :: Topology a =>
-- law_Topology_compatibility a1 a2

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
law_getNeighborhood :: Manifold a => a -> Neighborhood a -> Logic (Neighborhood a)
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

instance Topology Bool where
    type Neighborhood Bool = ()
    (==) a1 a2 = \_ -> a1 P.== a2

instance Topology (Discrete a) where
    type Neighborhood (Discrete a) = ()

instance Topology Float where
    type Neighborhood Float = Discrete (NonNegative Rational)
    isNeighbor a1 (a2,Discrete (NonNegative n)) = (toRational (P.abs (a1 P.- a2)) <= n) (Discrete $ NonNegative 0)

instance Topology Rational where
    type Neighborhood Rational = Discrete (NonNegative Rational)
    isNeighbor a1 (a2,Discrete (NonNegative n)) = (P.abs (a1 P.- a2) <= n) (Discrete $ NonNegative 0)

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

--------------------

class Topology a => Semigroup a where

    {-# MINIMAL (+) | plus #-}

    infixr 6 +
    (+) :: a -> a -> a
    a1+a2 = P.fst $ plus (a1,lowerBound) (a2,lowerBound)

    plus :: (a,Neighborhood a) -> (a,Neighborhood a) -> (a,Neighborhood a)
    plus (a1,n1) (a2,n2) = (a1+a2,sup n1 n2)

    neighborhood_Semigroup_error :: a -> a -> Neighborhood a
    neighborhood_Semigroup_error _ _ = lowerBound

    neighborhood_Semigroup_associative :: a -> a -> a -> Neighborhood a
    neighborhood_Semigroup_associative a1 a2 a3
        = sup (P.snd $ plus (a1+a2,neighborhood_Semigroup_error a1 a2) (a3,lowerBound))
              (P.snd $ plus (a3+a2,neighborhood_Semigroup_error a3 a2) (a1,lowerBound))

law_Semigroup_associative :: Semigroup a => a -> a -> a -> Logic a
law_Semigroup_associative a1 a2 a3 = (a1+a2)+a3 == a1+(a2+a3)

instance Semigroup Float where
    (+) = (P.+)

instance (Semigroup a, Semigroup b) => Semigroup (a,b) where
    (a1,b1)+(a2,b2) = (a1+a2,b1+b2)

    neighborhood_Semigroup_associative (a1,b1) (a2,b2) (a3,b3)
        = ( neighborhood_Semigroup_associative a1 a2 a3
          , neighborhood_Semigroup_associative b1 b2 b3
          )

instance Semigroup a => Semigroup [a] where
    (x:xr)+(y:yr) = x+y : xr+yr
    []    +ys     = ys
    xs    +[]     = xs

    neighborhood_Semigroup_associative as1 as2 as3
        = P.foldl sup lowerBound $ P.zipWith3 neighborhood_Semigroup_associative as1 as2 as3

--------------------

data Interval a where
    Interval :: Topology a => a -> Neighborhood a -> Interval a

instance Topology a => Topology (Interval a) where
    type Neighborhood (Interval a) = Neighborhood a

instance Semigroup (Interval Float) where
    (Interval a1 n1)+(Interval a2 n2) = Interval (a1+a2) (sup n1 n2)

----------------------------------------

class Semigroup a => Monoid a where
    zero :: a

    neighborhood_Monoid_zero :: a -> Neighborhood a
    neighborhood_Monoid_zero _ = lowerBound

law_Monoid_zero :: Monoid a => a -> Logic a
law_Monoid_zero a = zero+a == a

class Monoid a => Group a where
    {-# MINIMAL negate | (-) #-}
    negate :: a -> a
    negate a = zero - a

    (-) :: a -> a -> a
    a1-a2 = a1 + negate a2

class Group a => Ring a where
    one :: a
    (*) :: a -> a -> a

class Ring a => Field a where
    {-# MINIMAL reciprocal | (/) #-}
    reciprocal :: a -> a
    reciprocal a = one / a

    (/) :: a -> a -> a
    a1/a2 = a1 * reciprocal a2

-- type Hask = (->)
--
-- class Semigroup (cat :: * -> * -> *) a where
--     (+) :: cat a (cat a a)
--
-- instance Semigroup (->) Float where
--     (+) = (P.+)
--
-- instance Semigroup (->) b => Semigroup (->) (a -> b) where
--     (+) f1 f2 = \a -> f1 a + f2 a
--
-- instance Semigroup Top Float where
--     (+) = Top
--         { arrow = \a1 -> Top
--             { arrow = \a2 -> a1 P.+ a2
--             , inv = \_ nb -> nb
--             }
--         , inv = \a (_,nb) -> nb
--         }
--
-- instance (Semigroup (->) b, Semigroup Top b) => Semigroup (->) (Top a b) where
--     (+) (Top f1 inv1) (Top f2 inv2) = Top
--         { arrow = f1 + f2
--         , inv = undefined
--         }

