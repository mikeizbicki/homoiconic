module Main
    where

import Prelude

data LogicKind = LK_Bool

type Logic a = LogicRep a (LogicKind' a)

type family LogicRep a (k :: LogicKind) where
    LogicRep a LK_Bool = Bool

class Topology a where
--     type Neighbor a :: *
    type LogicKind' :: LogicKind

    isNeighbor :: a -> a -> Logic a
