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

-- withNeighborhood :: Poset a => (Community a -> Bool) -> a -> (Community (Neighborhood a) -> Bool)
withNeighborhood :: Poset a => (Community a -> Bool) -> a -> Logic a
withNeighborhood f a = \cna -> f (NCons a cna)

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
    , Lattice (Neighborhood a)
    ) => Topology a
        where

    {-# MINIMAL (==) | isNeighbor #-}

    type Neighborhood a
    isNeighbor :: a -> a -> Logic a
    isNeighbor = (==)

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

law_Topology_inf ::
    Topology a => a -> a -> Community (Neighborhood a) -> Community (Neighborhood a) -> Bool
law_Topology_inf a1 a2 c1 c2
    = isNeighbor a1 a2 (c1 && c2)
    ==> ( isNeighbor a1 a2 c1
       || isNeighbor a1 a2 c2
        )

instance Topology Float where
    type Neighborhood Float = Discrete (NonNegative Float)
    isNeighbor = fromMetric_isNeighbor

instance Topology Rational where
    type Neighborhood Rational = Discrete (NonNegative Rational)
    isNeighbor = fromMetric_isNeighbor

instance Topology Integer where
    type Neighborhood Integer = Discrete (NonNegative Integer)
    isNeighbor = fromMetric_isNeighbor

instance Topology a => Topology (Discrete a) where
    type Neighborhood (Discrete a) = ()
    isNeighbor (Discrete a1) (Discrete a2) _ = isNeighbor a1 a2 lowerBound

instance Topology a => Topology (NonNegative a) where
    type Neighborhood (NonNegative a) = Neighborhood a
    isNeighbor (NonNegative a1) (NonNegative a2) = isNeighbor a1 a2

----------------------------------------

class Topology a => Manifold a where
    getNeighbor :: a -> Neighborhood a -> a

    getNeighborhood :: a -> a -> Neighborhood a

law_Manifold_edge :: Manifold a => a -> Neighborhood a -> Neighborhood a -> Logic (Neighborhood a)
law_Manifold_edge a n1 n2 = withNeighborhood (isNeighbor a a') n1'
                    && not (withNeighborhood (isNeighbor a a') n2')
    where
        n1' = inf n1 n2
        n2' = sup n1 n2
        a'  = getNeighbor a n1'

-- law_getNeighborhood :: Manifold a => a -> a -> Logic a
-- law_getNeighborhood a1 a2 = getNeighbor a1 (getNeighborhood a1 a2) == a2
law_getNeighborhood :: Manifold a => a -> Neighborhood a -> Logic (Neighborhood a)
law_getNeighborhood a1 n1 = getNeighborhood a1 (getNeighbor a1 n1) == n1

----------------------------------------

class (Topology (Scalar a), Num (Scalar a), Lattice (Scalar a)) => Metric a where
    type Scalar a
    distance :: a -> a -> Scalar a

fromMetric_isNeighbor ::
    ( Neighborhood a~Discrete (NonNegative (Scalar a))
    , Metric a
    ) => a -> a -> Logic a
fromMetric_isNeighbor a1 a2 (n1 `NCons` n2) = ((Discrete $ NonNegative $ distance a1 a2) <= n1) n2

instance Metric Float where
    type Scalar Float = Float
    distance a1 a2 = P.abs $ a1 P.- a2

instance Metric Rational where
    type Scalar Rational = Rational
    distance a1 a2 = P.abs $ a1 P.- a2

instance Metric Integer where
    type Scalar Integer = Integer
    distance a1 a2 = P.abs $ a1 P.- a2

----------------------------------------

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

-- | FIXME:
instance Topology a => Lattice [a]

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

ifThenElse :: LowerBounded a => (a -> Bool) -> b -> b -> b
ifThenElse f a1 a2 = case f lowerBound of
    True -> a1
    False -> a2

instance Show (Community a -> Bool) where
    show f = show $ f lowerBound

--------------------------------------------------------------------------------

class Topology a => Semigroup a where

    infixr 6 +
    (+) :: a -> a -> a

    neighborhood_Semigroup_associative :: a -> a -> a -> Neighborhood a
    neighborhood_Semigroup_associative _ _ _ = lowerBound

--     plus :: (a,Neighborhood a) -> (a, Neighborhood a) -> (a,Neighborhood a)
--
--     neighborhood_Semigroup_error :: a -> a -> Neighborhood a
--     neighborhood_Semigroup_error _ _ = lowerBound
--
--     neighborhood_Semigroup_associative :: a -> a -> a -> Neighborhood a
--     neighborhood_Semigroup_associative a1 a2 a3
--         = sup (P.snd $ plus (a1+a2,neighborhood_Semigroup_error a1 a2) (a3,lowerBound))
--               (P.snd $ plus (a3+a2,neighborhood_Semigroup_error a3 a2) (a1,lowerBound))

law_Semigroup_associative :: Semigroup a => a -> a -> a -> Logic a
law_Semigroup_associative a1 a2 a3 = (a1+a2)+a3 == a1+(a2+a3)

-- | Category of topological spaces.
-- The morphisms are continuous functions.
--
-- See <wikipedia https://en.wikipedia.org/wiki/Category_of_topological_spaces>
-- for more details.
data Top a b where
    Top ::
        ( Topology a
        , Topology b
        , Neighborhood (Neighborhood a)~Neighborhood (Neighborhood b)
        ) => { arrow :: a -> b
             , inv :: a -> Neighborhood b -> Neighborhood a
             }
        -> Top a b

comp :: forall a b c. Top b c -> Top a b -> Top a c
comp (Top f1 inv1) (Top f2 inv2) = Top
    { arrow = f1 . f2
    , inv = \a nc -> inv2 a (inv1 (f2 a) nc)
    }

prop_Top :: Top a b -> a -> a -> Neighborhood b -> Logic (Neighborhood a)
prop_Top (Top f inv) a1 a2 nb
    = (withNeighborhood (  a1 `isNeighbor`   a2) (inv a1 nb))
  ==> (withNeighborhood (f a1 `isNeighbor` f a2) nb)
