{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeApplications #-}

module Topology2
    where

import qualified Prelude as P
import LocalPrelude
import Lattice

import Test.Framework
import Test.Framework.Runners.Console
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck.Arbitrary

import Debug.Trace

----------------------------------------

type Logic a = Community (Neighborhood a) -> Bool

data Community a where
    NNil    :: Community a
    NCons   :: Poset a => a -> Community (Neighborhood a) -> Community a
    NBranch :: Community a -> Community b -> Community (a,b)

instance Show (Community a) where
    show (NNil) = "NNil"
    show (NCons a na) = "NCons (a) ("++show na++")"
    show (NBranch ca cb) = "NBranch ("++show ca++") ("++show cb++")"

instance Poset (Community a) where
    inf NNil _ = NNil
    inf _ NNil = NNil
    inf (NCons na1 c1) (NCons na2 c2) = NCons (inf na1 na2) (inf c1 c2)
    inf (NBranch a1 b1) (NBranch a2 b2) = NBranch (inf a1 a2) (inf b1 b2)

instance LowerBounded (Community a) where
    lowerBound = NNil

-- withNeighborhood :: Poset a => (Community a -> Bool) -> a -> (Community (Neighborhood a) -> Bool)
withNeighborhood :: Poset a => (Community a -> Bool) -> a -> Logic a
withNeighborhood f a = \cna -> f (NCons a cna)

mkTuple :: LowerBounded a => Community a -> (a, Community (Neighborhood a))
mkTuple NNil          = (lowerBound,NNil)
mkTuple (NCons a cna) = (a,cna)
-- mkTuple (NBranch a b) = ((na,nb),NBranch ca cb)
--     where
--         (na,ca) = mkTuple a
--         (nb,cb) = mkTuple b

--------------------

class
    ( Topology (Neighborhood a)
    , LowerBounded (Neighborhood a)
    , Lattice (Neighborhood a)
    ) => Topology a
        where

    {-# MINIMAL (==) | isNeighbor #-}

    type Neighborhood a
    isNeighbor :: a -> a -> Logic a
    isNeighbor = (==)

    infixr 4 ==
    (==) :: a -> a -> Logic a
    (==) a1 a2 = isNeighbor a1 a2 || isNeighbor a2 a1

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

law_Topology_inf ::
    Topology a => a -> a -> Community (Neighborhood a) -> Community (Neighborhood a) -> Bool
law_Topology_inf a1 a2 c1 c2
    = isNeighbor a1 a2 (c1 && c2)
    ==> ( isNeighbor a1 a2 c1
       || isNeighbor a1 a2 c2
        )

instance Topology Float where
    type Neighborhood Float = Discrete (NonNegative Float)
    isNeighbor a1 a2 c = distance a1 a2 P.<= n1
        where
            (Discrete (NonNegative n1),n2) = mkTuple c
--     isNeighbor = fromMetric_isNeighbor

instance Topology Rational where
    type Neighborhood Rational = Discrete (NonNegative Rational)
    isNeighbor = fromMetric_isNeighbor

instance Topology Integer where
    type Neighborhood Integer = Discrete (NonNegative Integer)
    isNeighbor = fromMetric_isNeighbor

instance Topology a => Topology (Discrete a) where
    type Neighborhood (Discrete a) = ()
    isNeighbor (Discrete a1) (Discrete a2) _ = isNeighbor a1 a2 lowerBound

instance Topology a => Topology (NonNegative a) where
    type Neighborhood (NonNegative a) = Neighborhood a
    isNeighbor (NonNegative a1) (NonNegative a2) = isNeighbor a1 a2

--------------------

-- | Category of topological spaces.
-- The morphisms are continuous functions.
--
-- See <wikipedia https://en.wikipedia.org/wiki/Category_of_topological_spaces>
-- for more details.
data Top a b where
    Top ::
        ( Topology a
        , Topology b
        , Neighborhood (Neighborhood a)~Neighborhood (Neighborhood b)
        ) => { arrow :: a -> b
             , inv :: a -> Neighborhood b -> Neighborhood a
             }
        -> Top a b

comp :: forall a b c. Top b c -> Top a b -> Top a c
comp (Top f1 inv1) (Top f2 inv2) = Top
    { arrow = f1 . f2
    , inv = \a nc -> inv2 a (inv1 (f2 a) nc)
    }

prop_Top :: Top a b -> a -> a -> Neighborhood b -> Logic (Neighborhood a)
prop_Top (Top f inv) a1 a2 nb
    = (withNeighborhood (  a1 `isNeighbor`   a2) (inv a1 nb))
  ==> (withNeighborhood (f a1 `isNeighbor` f a2) nb)

----------------------------------------

class Topology a => Manifold a where
    getNeighbor :: a -> Neighborhood a -> a

    getNeighborhood :: a -> a -> Neighborhood a

law_Manifold_edge :: Manifold a => a -> Neighborhood a -> Neighborhood a -> Logic (Neighborhood a)
law_Manifold_edge a n1 n2 = withNeighborhood (isNeighbor a a') n1'
                    && not (withNeighborhood (isNeighbor a a') n2')
    where
        n1' = inf n1 n2
        n2' = sup n1 n2
        a'  = getNeighbor a n1'

-- law_getNeighborhood :: Manifold a => a -> a -> Logic a
-- law_getNeighborhood a1 a2 = getNeighbor a1 (getNeighborhood a1 a2) == a2
law_getNeighborhood :: Manifold a => a -> Neighborhood a -> Logic (Neighborhood a)
law_getNeighborhood a1 n1 = getNeighborhood a1 (getNeighbor a1 n1) == n1

----------------------------------------

class (Topology (Scalar a), Num (Scalar a), Lattice (Scalar a)) => Metric a where
    type Scalar a
    distance :: a -> a -> Scalar a

fromMetric_isNeighbor ::
    ( Neighborhood a~Discrete (NonNegative (Scalar a))
    , P.Eq (Scalar a)
    , Metric a
    ) => a -> a -> Logic a
fromMetric_isNeighbor a1 a2 (n1 `NCons` n2) = ((Discrete $ NonNegative $ distance a1 a2) <= n1) n2
fromMetric_isNeighbor a1 a2 NNil            = distance a1 a2 P.== 0 -- ((Discrete $ NonNegative $ distance a1 a2) <= lowerBound) lowerBound
-- fromMetric_isNeighbor a1 a2 NNil            = True -- ((Discrete $ NonNegative $ distance a1 a2) <= lowerBound) lowerBound

instance Metric Float where
    type Scalar Float = Float
    distance a1 a2 = P.abs $ a1 P.- a2

instance Metric Rational where
    type Scalar Rational = Rational
    distance a1 a2 = P.abs $ a1 P.- a2

instance Metric Integer where
    type Scalar Integer = Integer
    distance a1 a2 = P.abs $ a1 P.- a2

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

-- | FIXME:
instance Topology a => Lattice [a]

instance Topology a => Semigroup [a] where
    (+) = (P.++)

--------------------


instance (Topology a, Topology b) => Topology (a -> b) where
    type Neighborhood (a -> b) = ([a], Neighborhood b)
    (==) f g (NBranch (NCons xs _) nb) = go xs
                where
                    go (x:xs) = (f x==g x) nb && go xs
                    go []     = True

instance (Topology a, Topology b) => Topology (a,b) where
    type Neighborhood (a,b) = (Neighborhood a, Neighborhood b)
    (==) (a1,b1) (a2,b2) NNil            = (a1==a2) NNil && (b1==b2) NNil
    (==) (a1,b1) (a2,b2) (NBranch ea eb) = (a1==a2) ea   && (b1==b2) eb

instance Topology () where
    type Neighborhood () = ()
    (==) _ _ = \_ -> True

----------------------------------------

ifThenElse :: LowerBounded a => (a -> Bool) -> b -> b -> b
ifThenElse f a1 a2 = case f lowerBound of
    True -> a1
    False -> a2

instance Show (Community a -> Bool) where
    show f = show $ f lowerBound

--------------------------------------------------------------------------------

class Topology a => Semigroup a where

    infixr 6 +
    (+) :: a -> a -> a

    neighborhood_Semigroup_associative :: a -> a -> a -> Community (Neighborhood a)
    neighborhood_Semigroup_associative _ _ _ = lowerBound

--     plus :: (a,Neighborhood a) -> (a, Neighborhood a) -> (a,Neighborhood a)
--
--     neighborhood_Semigroup_error :: a -> a -> Neighborhood a
--     neighborhood_Semigroup_error _ _ = lowerBound
--
--     neighborhood_Semigroup_associative :: a -> a -> a -> Neighborhood a
--     neighborhood_Semigroup_associative a1 a2 a3
--         = sup (P.snd $ plus (a1+a2,neighborhood_Semigroup_error a1 a2) (a3,lowerBound))
--               (P.snd $ plus (a3+a2,neighborhood_Semigroup_error a3 a2) (a1,lowerBound))

law_Semigroup_associative :: Semigroup a => a -> a -> a -> Logic a
law_Semigroup_associative a1 a2 a3 = (a1+a2)+a3 == a1+(a2+a3)

instance Semigroup () where
    ()+()=()

instance Semigroup Integer where
    (+) = (P.+)

instance Semigroup Float where
    (+) = (P.+)
    neighborhood_Semigroup_associative _ _ _ = NCons (Discrete $ NonNegative 2e-2) NNil

--------------------

class cxt => Lawful (cxt :: Constraint) where
    lawful :: proxy cxt -> Test

instance (Lawful cxt1, Lawful cxt2) => Lawful (cxt1,cxt2) where
    lawful _ = testGroup "Tuple-2"
        [ lawful (Proxy::Proxy cxt1)
        , lawful (Proxy::Proxy cxt2)
        ]

instance (Lawful cxt1, Lawful cxt2, Lawful cxt3) => Lawful (cxt1,cxt2,cxt3) where
    lawful _ = testGroup "Tuple-3"
        [ lawful (Proxy::Proxy cxt1)
        , lawful (Proxy::Proxy cxt2)
        , lawful (Proxy::Proxy cxt3)
        ]

instance
    ( Show a
    , Arbitrary a
    , Semigroup a
    ) => Lawful (Semigroup a)
        where
    lawful _ = testGroup "Semigroup"
        [ testProperty "associative" (\(a1::a) (a2::a) (a3::a) ->
            (law_Semigroup_associative a1 a2 a3) (neighborhood_Semigroup_associative a1 a2 a3)
            )
        ]

instance
    ( Show a
    , Arbitrary a
    , Poset a
    ) => Lawful (Poset a)
        where
    lawful _ = testGroup "Poset"
        []

isLawful :: forall cxt. Lawful cxt => IO ()
isLawful = defaultMain [lawful (undefined::proxy cxt)]

--------------------

class (cxt a, cxt b) => Sub (cxt :: * -> Constraint) a b where
    embed' :: proxy cxt -> a -> b

instance cxt a => Sub cxt a a where
    embed' _ = P.id

instance Semigroup a => Sub Semigroup (NonNegative a) a where
    embed' _ (NonNegative a) = a

instance Semigroup a => Semigroup (NonNegative a)

-- class (Neighborhood a <: Neighborhood b) => a <: b where
class a <: b where
    embed :: a -> b

instance a <: a where
    embed a = a

instance Top a b <: (->) a b where
    embed = arrow

-- instance (Neighborhood a <: Neighborhood ()) => a <: () where
instance a <: () where
    embed _ = ()

instance (a,b) <: a where
    embed (a,b) = a

instance (a,b) <: b where
    embed (a,b) = b

law_SubType_hom :: forall a b cxt proxy.
    ( a <: b
    , cxt a
    , cxt b
    , Hom cxt
    ) => proxy cxt
      -> (a,b)
      -> HomInput cxt a b
      -> Logic b
law_SubType_hom cxt _ = law_hom cxt (embed :: a -> b)

law_SubType_mon :: forall a b cxt.
    ( a <: b
    , cxt a
    ) => (cxt b => ())
law_SubType_mon = ()

law_SubType_mon2 :: forall a b. a <: b => forall cxt. cxt a => (cxt b => ())
law_SubType_mon2 = ()

-- class SubType a b (cxt :: * -> Constraint) where
--     embed2 :: a -> b
--
-- instance SubType a a cxt where
--     embed2 a = a
--
-- instance cxt a => SubType (a,b) a cxt where
--     embed2 (a,b) = a

type family IfCxt (cxt :: Constraint) (arg:: Constraint) :: Constraint where
    IfCxt a a = ()
    IfCxt (cxt (a,b)) (cxt a) = cxt a

-- prop_Semigroup_homomorphism :: (Semigroup a, Semigroup b) => (a -> b) -> a -> a -> Logic b
-- prop_Semigroup_homomorphism f a1 a2 = f (a1+a2) == f a1 + f a2

class Hom (cxt :: Type -> Constraint) where
    type HomInput cxt a b
    law_hom :: (cxt a, cxt b) => proxy cxt -> (a -> b) -> HomInput cxt a b -> Logic b

instance Hom Semigroup where
    type HomInput Semigroup a b = (a,a)
    law_hom _ f (a1,a2) = f (a1+a2) == f a1 + f a2
