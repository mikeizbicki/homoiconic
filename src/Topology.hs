{-# LANGUAGE UndecidableSuperClasses #-}
module Topology
    where

import Prelude (fromInteger, Bool(..))
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


-- The paper "Two decades of fuzzy topology: basic ideas, notions, and results"
-- by A.P. Shostak gives a good overview of how this type of "fuzzy" topology could work.
class
    ( Topology (Neighborhood a)
    , LowerBounded (Neighborhood a)
--     , Lattice (Neighborhood a)
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
--                             && (f (c1||c2) == (f c1 || f c2))
                            && (lowerBound == f lowerBound)
    where
        f = (a1==a2)

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

-- instance Topology a => Lattice [a] where
--     sup xs ys = xs ++ ys

--------------------

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

instance Topology a => Topology (NonNegative a) where
    type Neighborhood (NonNegative a) = ()
    (==) (NonNegative a1) (NonNegative a2) _ = (a1==a2) undefined

instance Topology Float where
    type Neighborhood Float = NonNegative Float
    (==) a1 a2 = \(NonNegative n) -> P.abs (a1 P.- a2) P.<= n

--------------------------------------------------------------------------------

class Topology a => Metric a where
    type Scalar a
    distance :: a -> a -> Scalar a

instance Metric Float where
    type Scalar Float = Float
    distance a1 a2 = P.abs (a1 P.- a2)
