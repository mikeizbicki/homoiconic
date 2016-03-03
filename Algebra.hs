{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}

module Algebra
    where

import qualified Prelude as P
import LocalPrelude
import Lattice
import Tests
import Topology1 hiding (Lawful (..), Semigroup (..), isLawful)

import Test.SmallCheck.Series hiding (NonNegative)
import Test.Tasty
import qualified Test.Tasty.SmallCheck as SC
import qualified Test.Tasty.QuickCheck as QC
import Test.QuickCheck hiding (Testable,NonNegative)

import Debug.Trace

--------------------------------------------------------------------------------

class Topology a => Semigroup a where
    infixr 6 +
    (+) :: a -> a -> a

instance Lawful' Semigroup "associative" where
    type LawInput Semigroup "associative" a = (a,a,a)
    law _ _ _ (a1,a2,a3) = (a1+a2)+a3 == a1+(a2+a3)

instance Lawful Semigroup where
    laws _ p = [ mkLaw "associative" (associative p) ]
--     laws _ p = [ mkLaw' p "associative" associative' ]
--     laws _ (Proxy::Proxy a) = [ Law "associative" (associative @a) ]
        where
--             associative :: Semigroup a => proxy a -> (a,a,a) -> Logic a
--             associative _ (a1,a2,a3) = (a1+a2)+a3 == a1+(a2+a3)

            associative :: (Show a, Semigroup a) => proxy a -> (a,a,a) -> Logic a
            associative _ (a1,a2,a3) =  (a1+a2)+a3 == a1+(a2+a3)
--             associative _ (a1,a2,a3) = trace ("  law_a3="++show a3) $ (a1+a2)+a3 == a1+(a2+a3)

--             associative' :: Semigroup a => (a,a,a) -> Logic a
--             associative' (a1,a2,a3) = (a1+a2)+a3 == a1+(a2+a3)

-- mkLaw' :: Testable p => Proxy (a::k) -> LawName -> (forall (a::k). p -> n -> Bool) -> Law
-- mkLaw' (p::Proxy a) law f = Law law (f @a)

--------------------

instance Semigroup Float where
    (+) = (P.+)

instance {-# overlaps #-} Approximate' Semigroup "associative" Float where
    maxError _ _ _ (a1,a2,a3) = Discrete $ NonNegative $ 2e-2

instance {-# OVERLAPS #-} Approximate Semigroup Float where
    maxUnlawful _ _ = [ ErrorBound "associative" associator ]
        where
--             associator :: (Float) -> Neighborhood Float
--             associator (a3) = trace ("unlaw_a3="++show a3) $ Discrete $ NonNegative $ 2e2

            associator :: (Float,Float,Float) -> Neighborhood Float
            associator (_,_,a3) = trace ("unlaw_a3="++show a3) $ Discrete $ NonNegative $ 2e-2

--     maxUnlawful _ _ = [ ErrorBound "associative" $ \(a1::Float,a2::Float,a3::Float) -> Discrete $ NonNegative $ 2e-10]
--     maxUnlawful _ _ = [ ErrorBound "associative" $ Discrete $ NonNegative $ 2e-3)]

instance Semigroup Double where
    (+) = (P.+)

instance {-# OVERLAPS #-} Approximate Semigroup Double where
    maxUnlawful _ _ = [ ErrorBound "associative" associator ]
        where
            associator :: (Float,Float,Float) -> Neighborhood Float
            associator (_,_,a3) = trace ("a3="++show a3) $ Discrete $ NonNegative $ 2e-3

--------------------

instance (Semigroup a, Semigroup b) => Semigroup (a,b) where
    (a1,b1)+(a2,b2) = (a1+a2,b1+b2)

instance Semigroup () where
    ()+()=()

instance Semigroup Int where
    (+) = (P.+)

instance Semigroup Integer where
    (+) = (P.+)

--------------------

instance Topology a => Semigroup [a] where
    (+) = (P.++)

-- instance Semigroup a => Semigroup [a] where
--     (x:xr)+(y:yr) = x+y : xr+yr
--     []    +ys     = ys
--     xs    +[]     = xs

--------------------

data Interval a where
    Interval :: Topology a => a -> Neighborhood a -> Interval a

instance Topology a => Topology (Interval a) where
    type Neighborhood (Interval a) = Neighborhood a

instance Semigroup (Interval Float) where
    (Interval a1 n1)+(Interval a2 n2) = Interval (a1+a2) (sup n1 n2)

----------------------------------------

class Semigroup a => Monoid a where
    zero :: a

    neighborhood_Monoid_zero :: a -> Neighborhood a
    neighborhood_Monoid_zero _ = lowerBound

law_Monoid_zero :: Monoid a => a -> Logic a
law_Monoid_zero a = zero+a == a

class Monoid a => Group a where
    {-# MINIMAL negate | (-) #-}
    negate :: a -> a
    negate a = zero - a

    (-) :: a -> a -> a
    a1-a2 = a1 + negate a2

class Group a => Ring a where
    one :: a
    (*) :: a -> a -> a

class Ring a => Field a where
    {-# MINIMAL reciprocal | (/) #-}
    reciprocal :: a -> a
    reciprocal a = one / a

    (/) :: a -> a -> a
    a1/a2 = a1 * reciprocal a2

-- type Hask = (->)
--
-- class Semigroup (cat :: * -> * -> *) a where
--     (+) :: cat a (cat a a)
--
-- instance Semigroup (->) Float where
--     (+) = (P.+)
--
-- instance Semigroup (->) b => Semigroup (->) (a -> b) where
--     (+) f1 f2 = \a -> f1 a + f2 a
--
-- instance Semigroup Top Float where
--     (+) = Top
--         { arrow = \a1 -> Top
--             { arrow = \a2 -> a1 P.+ a2
--             , inv = \_ nb -> nb
--             }
--         , inv = \a (_,nb) -> nb
--         }
--
-- instance (Semigroup (->) b, Semigroup Top b) => Semigroup (->) (Top a b) where
--     (+) (Top f1 inv1) (Top f2 inv2) = Top
--         { arrow = f1 + f2
--         , inv = undefined
--         }

