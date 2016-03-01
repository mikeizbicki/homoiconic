{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveGeneric #-}

module Tests
    where

import qualified Prelude as P
import LocalPrelude
import Lattice
import Union
import Topology2 hiding (Lawful(..))

import Test.Framework
import Test.Framework.Runners.Console
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Property

import GHC.Generics
import Debug.Trace

--------------------------------------------------------------------------------

data family Dict (cxt :: Constraint)

data instance Dict (Semigroup a) = Dict_Semigroup
    deriving Generic

data instance Dict (Topology a) = Dict_Topology
    deriving Generic

----------------------------------------

class GenericClass (cxt::Constraint) where
    type OpType cxt
    op :: Proxy cxt -> OpType cxt

instance Semigroup a => GenericClass (Semigroup a) where
    type OpType (Semigroup a) = (a -> a -> a)
    op _ = (+)

--------------------------------------------------------------------------------

class LawClass p
-- instance LawClass p

instance LawClass b => LawClass (a -> b)

data Law where
    Law :: forall p. LawClass p => p -> Law


mkLaw :: LawClass p => String -> p -> Law
mkLaw _ = Law

-- |
--
-- See "Heterogenous Algebras" by Birkhoff and Lipson
class cxt => Lawful cxt where
    laws :: proxy cxt -> [Law]

instance Semigroup a => Lawful (Semigroup a) where
    laws _ = [ mkLaw "associative" associative ]
        where
            associative :: a -> a -> a -> Logic a
            associative a1 a2 a3 = (a1+a2)+a3 == a1+(a2+a3)

instance Topology a => Lawful (Topology a) where
    laws _ = [ mkLaw "inf" (law_Topology_inf @a) ]

