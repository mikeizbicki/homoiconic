{-# LANGUAGE UndecidableSuperClasses #-}

module Topology
    where

import qualified Prelude as P
import LocalPrelude
import Lattice

----------------------------------------

type Logic a = NeighborhoodChain a -> Bool

type NeighborhoodChain a = NeighborhoodChain_ (Neighborhood a)
type family NeighborhoodChain_ a where
    NeighborhoodChain_ () = ()
    NeighborhoodChain_ a = (a, NeighborhoodChain_ (Neighborhood a))

class
    ( Topology (Neighborhood a)
    , Neighborhood (Neighborhood (Neighborhood (Neighborhood a))) ~ ()
    , LowerBounded (NeighborhoodChain a)
    , Lattice (NeighborhoodChain a)
    ) => Topology a
        where

    type Neighborhood a
    isNeighbor :: a -> a -> Logic a

    infixr 4 ==
    (==) :: a -> a -> Logic a
    (==) a1 a2 = isNeighbor a1 a2 || isNeighbor a2 a1

    infixr 4 <=
    (<=) :: Poset a => a -> a -> Logic a
    (<=) a1 a2 = a1 == inf a1 a2

----------------------------------------

instance Topology Float where
    type Neighborhood Float = Discrete (NonNegative Rational)
    isNeighbor a1 a2 (r,n) = ((Discrete $ NonNegative $ toRational $ P.abs $ a1 P.- a2) <= r) n

instance Topology Rational where
    type Neighborhood Rational = Discrete (NonNegative Rational)
    isNeighbor a1 a2 (Discrete (NonNegative r),n) = ((P.abs $ a1 P.- a2) P.<= r)

instance Topology () where
    type Neighborhood () = ()
    isNeighbor _ _ () = True

instance Topology a => Topology (Discrete a) where
    type Neighborhood (Discrete a) = ()
    isNeighbor (Discrete a1) (Discrete a2) _ = isNeighbor a1 a2 lowerBound

instance Topology a => Topology (NonNegative a) where
    type Neighborhood (NonNegative a) = Neighborhood a
    isNeighbor (NonNegative a1) (NonNegative a2) = isNeighbor a1 a2

----------------------------------------

ifThenElse :: LowerBounded a => (a -> Bool) -> b -> b -> b
ifThenElse f a1 a2 = case f lowerBound of
    True -> a1
    False -> a2

-- data Log a where
--     Log :: LowerBounded a => (a -> Bool) -> Log a

-- ifThenElse :: Log a -> b -> b -> b
-- ifThenElse (Log f) a1 a2 = case f lowerBound of
--     True -> a1
--     False -> a2

-- instance P.Show (Log a) where
--     show f = if f then "true" else "false"

