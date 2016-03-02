{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveGeneric #-}

module Category
    where

import qualified Prelude as P
import LocalPrelude
import Lattice
import Topology2

-- import Test.Framework
-- import Test.Framework.Runners.Console
-- import Test.Framework.Providers.QuickCheck2
-- import Test.QuickCheck.Arbitrary

import GHC.Generics
import Debug.Trace

----------------------------------------

class Category (cat :: obj -> obj -> *) where
    type ValidObject cat (a::obj) :: Constraint

    id :: ValidObject cat a => cat a a
    (.) :: cat b c -> cat a b -> cat a c

data Cat cxt a b where
    Cat :: (cxt a, a~b) => a -> Cat cxt a b

instance Category (Cat P.Monoid) where
    type ValidObject (Cat P.Monoid) a = P.Monoid a
    id = Cat P.mempty
    (Cat a1).(Cat a2) = Cat (a1 `P.mappend` a2)

----------------------------------------

class Cxt k => Cxt (a::k)

instance Cxt Type

instance Cxt Nat

data App cxt a where
--     AppCon :: {-forall cxt a. cxt a =>-} a -> App cxt a
    AppCon :: forall cxt a. cxt a => a -> App cxt a

data (a::App cxt ka) ~> (b::App cxt kb) where
--     Id :: forall cxt a. cxt a => (a -> a) -> (AppCon a ~> AppCon a)
--     Id :: forall cxt a. (a -> a) -> (App cxt a ~> App cxt a)
--     Arrow :: forall a b cxt c d. (cxt a, cxt b) => (a -> b) -> ((c::App cxt) ~> (d::App cxt))

instance Category (~>) where
    type ValidObject (~>) a = ()
--     id = AppCon P.id

-- class Foo (a :: Test cxt) where
--     foo :: a -> a
