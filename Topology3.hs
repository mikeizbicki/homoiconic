{-# LANGUAGE UndecidableSuperClasses #-}

module Topology
    where

import qualified Prelude as P
import LocalPrelude
import Lattice

----------------------------------------

type Logic a = Logic_ (Neighborhood a)

type family Logic_ a where
    Logic_ () = Bool
    Logic_ a  = a -> Bool

class IfThenElse a where
    ifThenElse :: a -> b -> b -> b

instance IfThenElse Bool
instance LowerBounded a => IfThenElse (a -> Bool)

class (LowerBounded (Neighborhood a)) => Topology a where
    type Neighborhood a :: *

    isNeighbor :: a -> a -> Logic a
