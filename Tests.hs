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

import Test.SmallCheck.Series
import Test.Tasty
import qualified Test.Tasty.SmallCheck as SC
import qualified Test.Tasty.QuickCheck as QC
import Test.QuickCheck hiding (Testable)

--------------------------------------------------------------------------------

type LawName = String

class Lawful (cxt :: * -> Constraint) where
    laws :: (Testable b, cxt b) => Proxy cxt -> Proxy b -> [Law]

data Law where
    Law :: Testable p => LawName -> (p -> (n -> Bool)) -> Law

type Testable p = (Arbitrary p, CoArbitrary p) --SC.Testable IO p, QC.Testable p)

--------------------

mkLaw :: Testable p => Proxy a -> LawName -> (Proxy a -> p -> n -> Bool) -> Law
mkLaw p law f = Law law (f p)

--------------------

-- class (Lawful cxt, cxt a) => Approximate cxt a where
--     maxUnlawful :: cxt a => Proxy cxt -> Proxy a -> [ (LawName, Neighborhood a) ]
--
-- instance {-# OVERLAPPABLE #-} (Lawful cxt, cxt a) => Approximate cxt a where
--     maxUnlawful _ _ = []

-- getMaxUnlawful :: LowerBounded a => proxy (cxt::Constraint) -> LawName -> a
-- getMaxUnlawful p lawWanted = go $ maxUnlawful p
--     where
--         go [] = lowerBound
--         go ((law,a):xs) = if law==lawWanted
--             then a
--             else go xs

