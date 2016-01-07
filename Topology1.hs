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

class LowerBounded (Neighborhood a) => Topology a where
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

instance Topology Float where
    type Neighborhood Float = NonNegative Rational
    isNeighbor a1 (a2,NonNegative n) = (toRational (P.abs (a1 P.- a2)) <= n) (NonNegative 0)

instance Topology Rational where
    type Neighborhood Rational = NonNegative Rational
    isNeighbor a1 (a2,NonNegative n) = (P.abs (a1 P.- a2) <= n) (NonNegative 0)

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

-- class Topology a => Semigroup a where
--
--     infixr 6 +
--     (+) :: a -> a -> a
--
--     neighborhood_Semigroup_associative :: a -> a -> a -> Neighborhood a
--     neighborhood_Semigroup_associative _ _ _ = lowerBound
--
-- law_Semigroup_associative :: Semigroup a => a -> a -> a -> Logic a
-- law_Semigroup_associative a1 a2 a3 = (a1+a2)+a3 == a1+(a2+a3)

type Hask = (->)

class Semigroup (cat :: * -> * -> *) a where
    (+) :: cat a (cat a a)

instance Semigroup (->) Float where
    (+) = (P.+)

instance Semigroup (->) b => Semigroup (->) (a -> b) where
    (+) f1 f2 = \a -> f1 a + f2 a

instance Semigroup Top Float where
    (+) = Top
        { arrow = \a1 -> Top
            { arrow = \a2 -> a1 P.+ a2
            , inv = \_ nb -> nb
            }
        , inv = \a (_,nb) -> nb
        }

instance (Semigroup (->) b, Semigroup Top b) => Semigroup (->) (Top a b) where
    (+) (Top f1 inv1) (Top f2 inv2) = Top
        { arrow = f1 + f2
        , inv = undefined
        }

