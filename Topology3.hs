{-# LANGUAGE UndecidableSuperClasses #-}

module Topology3
    where

import Prelude (fromInteger)
import qualified Prelude as P
import LocalPrelude
import Lattice

--------------------------------------------------------------------------------

ifThenElse :: LowerBounded b => (b -> Bool) -> a -> a -> a
ifThenElse f a1 a2 = case f lowerBound of
    True  -> a1
    False -> a2

----------------------------------------

-- newtype SimpleLogic a = SimpleLogic (XXX a -> Bool)
--
-- instance Poset (SimpleLogic a) where
--     inf (SimpleLogic f1) (SimpleLogic f2) = SimpleLogic $ inf f1 f2
--
-- instance Lattice (SimpleLogic a) where
--     sup (SimpleLogic f1) (SimpleLogic f2) = SimpleLogic $ sup f1 f2
--
-- instance LowerBounded (SimpleLogic a) where
--     lowerBound = SimpleLogic lowerBound
--
-- instance UpperBounded (SimpleLogic a) where
--     upperBound = SimpleLogic upperBound
--
-- instance Complemented (SimpleLogic a) where
--     not (SimpleLogic a) = SimpleLogic (not a)
--
-- instance Topology (SimpleLogic a) where
--     -- FIXME

----------------------------------------

class Topology a where
    type Neighborhood a
    evalLogic :: a -> Neighborhood a -> Bool

class
    ( Complemented (Logic a)
    , Topology (Logic a)
    , Eq (Logic a)
    ) => Eq a
        where

    type Logic a

    infixr 4 ==
    (==) :: a -> a -> Logic a

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

----------

instance Eq b => Eq (a -> b) where
    type Logic (a -> b) = ([a], Neighborhood (Logic b)) -> Bool
    (==) f g (xs,nb) = go xs
                where
                    go :: [a] -> Bool
                    go (x:xs) = evalLogic (f x==g x) nb && go xs
                    go []     = True

instance Topology (a -> Bool) where
    type Neighborhood (a -> Bool) = a
    evalLogic f = f

instance Eq Bool where
    type Logic Bool = Bool
    (==) = (P.==)

instance Topology Bool where
    type Neighborhood Bool = ()
    evalLogic b _ = b
