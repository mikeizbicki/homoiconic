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
import Topology1 hiding (Lawful (..), Semigroup (..), isLawful)

import Test.SmallCheck.Series
import Test.Tasty
import qualified Test.Tasty.SmallCheck as SC
import qualified Test.Tasty.QuickCheck as QC
import Test.QuickCheck hiding (Testable)

--------------------------------------------------------------------------------

type LawName = String

class Lawful (cxt :: * -> Constraint) where
    laws :: (Testable a, cxt a) => Proxy cxt -> Proxy a -> [Law a]

data Law a where
--     Law :: (LowerBounded n, Testable p) => LawName -> (p -> (n -> Bool)) -> Law
--     Law :: (LowerBounded (Neighborhood a), Testable p) => LawName -> (p -> Neighborhood a -> Bool) -> Law a
    Law :: Testable p => LawName -> (p -> Logic a) -> Law a

type Testable p = (Show p, Arbitrary p, CoArbitrary p) --SC.Testable IO p, QC.Testable p)

--------------------

mkLaw ::
    ( LowerBounded (Neighborhood a)
    , Testable p
    ) => Proxy a
      -> LawName
      -> (Proxy a -> p -> Logic a)
      -> Law a
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


getMaxUnlawful :: Approximate cxt a
    => Proxy (cxt :: * -> Constraint)
    -> Proxy a
    -> LawName
    -> Community a
getMaxUnlawful pcxt pa lawWanted = go $ maxUnlawful pcxt pa
    where
        go [] = lowerBound
        go ((law,a):xs) = if law==lawWanted
            then a
            else go xs

isLawful :: forall cxt a. (Testable a, Approximate cxt a) => Proxy cxt -> Proxy a -> IO ()
isLawful pcxt pa = defaultMain $ testGroup "isLaw" $ map go $ laws pcxt pa
    where
        go (Law name prop) = QC.testProperty name (\p -> prop p $ getMaxUnlawful pcxt pa name)
--         go (Law name prop) = QC.testProperty name (\p -> prop p lowerBound)

class (Lawful cxt, Topology a, cxt a) => Approximate cxt a where
    maxUnlawful :: cxt a => Proxy cxt -> Proxy a -> [ (LawName, Neighborhood a) ]

instance {-# OVERLAPPABLE #-} (Lawful cxt, Topology a, cxt a) => Approximate cxt a where
    maxUnlawful _ _ = []

instance {-# OVERLAPS #-}
    ( Approximate cxt a
    , Approximate cxt b
    , cxt (a,b)
    ) => Approximate cxt (a,b) where

    maxUnlawful p1 _ = go
        (maxUnlawful p1 (Proxy::Proxy a))
        (maxUnlawful p1 (Proxy::Proxy b))
        where
            go as@((lawa,na):ar) bs@((lawb,nb):br) = case P.compare lawa lawb of
                P.EQ -> (lawa,(na,nb)):go ar br
                P.LT -> (lawa,(na,lowerBound)):go ar bs
                P.GT -> (lawa,(lowerBound,nb)):go as br

            go ((lawa,na):ar) [] = (lawa,(na,lowerBound)):go ar []
            go [] ((lawb,nb):br) = (lawb,(lowerBound,nb)):go [] br
            go [] [] = []
