{-# LANGUAGE CPP #-}
{-# LANGUAGE DefaultSignatures #-}

module Lattice
    where

import Prelude (fromInteger, Functor(..), Foldable(..))
import qualified Prelude as P
import LocalPrelude
import FAlgebra98

--------------------------------------------------------------------------------

class Poset a where
    inf :: a -> a -> a

mkFAlgebra98 ''Poset

infixr 3 &&
(&&) :: Poset a => a -> a -> a
(&&) = inf

instance Variety98 Poset where
    laws = [ associative (&&), commutative (&&), idempotent (&&) ]

#define mkPoset(x) \
instance Poset x where inf = P.min

mkPoset(Float)
mkPoset(Double)
mkPoset(Rational)
mkPoset(Integer)
mkPoset(Int)
mkPoset(Bool)
mkPoset(Char)

--------------------

class Poset a => LowerBounded a where
    lowerBound :: a

mkFAlgebra98 ''LowerBounded

instance Variety98 LowerBounded where
    laws =
        [ Law
            { lawName = "lowerBounded"
            , lhs = lowerBound && var1
            , rhs = lowerBound
            }
        ]

# define mkLattice(x) \
instance Lattice x where sup = P.max

mkLattice(Float)
mkLattice(Double)
mkLattice(Rational)
mkLattice(Integer)
mkLattice(Int)
mkLattice(Bool)
mkLattice(Char)

--------------------

class Poset a => Lattice a where
    sup :: a -> a -> a

mkFAlgebra98 ''Lattice

infixr 3 ||
(||) :: Lattice a => a -> a -> a
(||) = sup

instance Variety98 Lattice where
    laws =
        [ associative (||)
        , commutative (||)
        , idempotent (||)
        , Law
            { lawName = "absorption_inf"
            , lhs = var1 && (var1 || var2)
            , rhs = var1
            }
        , Law
            { lawName = "absorption_sup"
            , lhs = var1 || (var1 && var2)
            , rhs = var1
            }
        ]

#define mkLowerBounded(x) \
instance LowerBounded x where lowerBound = P.minBound

mkLowerBounded(Bool)
mkLowerBounded(Char)

--------------------

class Lattice a => UpperBounded a where
    upperBound :: a

mkFAlgebra98 ''UpperBounded

instance Variety98 UpperBounded where
    laws =
        [ Law
            { lawName = "upperBounded"
            , lhs = upperBound || var1
            , rhs = upperBound
            }
        ]

#define mkUpperBounded(x) \
instance UpperBounded x where upperBound = P.maxBound

mkUpperBounded(Bool)
mkUpperBounded(Char)

--------------------

class (LowerBounded a, UpperBounded a) => Complemented a where
    not :: a -> a

mkFAlgebra98 ''Complemented

-- NOTE:
-- These laws are considerably weaker than the laws that use quantifiers.
-- Because of our definition of Variety (and that quantifiers make quickcheck less effective)
-- we don't use the stronger laws.
instance Variety98 Complemented where
    laws =
        [ Law
            { lawName = "complement_inf"
            , lhs = not upperBound
            , rhs = lowerBound
            }
        , Law
            { lawName = "complement_sup"
            , lhs = not lowerBound
            , rhs = upperBound
            }
        ]

instance Complemented Bool where
    not True = False
    not False = True

--------------------

class (LowerBounded a, UpperBounded a) => Heyting a where
    infixr 3 ==>
    (==>) :: a -> a -> a

    default (==>) :: Complemented a => a -> a -> a
    (==>) = modusPonens

modusPonens :: Complemented b => b -> b -> b
modusPonens b1 b2 = not b1 || b2

mkFAlgebra98 ''Heyting

instance Variety98 Heyting where
    laws =
        [ Law
            { lawName = "Heyting_upperBound"
            , lhs = var1 ==> var1
            , rhs = upperBound
            }
        , Law
            { lawName = "Heyting_infleft"
            , lhs = var1 && (var1 ==> var2)
            , rhs = var1 && var2
            }
        , Law
            { lawName = "Heyting_infright"
            , lhs = var2 && (var1 ==> var2)
            , rhs = var2
            }
        , Law
            { lawName = "Heyting_distributive"
            , lhs = var1 ==> (var2 && var3)
            , rhs = (var1 ==> var2) && (var1 ==> var3)
            }
        ]

instance Heyting Bool

--------------------------------------------------------------------------------

instance Poset b => Poset (a -> b) where
    inf f g = \a -> inf (f a) (g a)

instance Lattice b => Lattice (a -> b) where
    sup f g = \a -> sup (f a) (g a)

instance LowerBounded b => LowerBounded (a -> b) where
    lowerBound = \a -> lowerBound

instance UpperBounded b => UpperBounded (a -> b) where
    upperBound = \a -> upperBound

instance Complemented b => Complemented (a -> b) where
    not f = \a -> not (f a)

instance Heyting b => Heyting (a -> b) where
    f ==> g = \a -> f a ==> g a

--------------------

instance (Poset a, Poset b) => Poset (a,b) where
    inf (a1,b1) (a2,b2) = (inf a1 a2, inf b1 b2)

instance (Lattice a, Lattice b) => Lattice (a,b) where
    sup (a1,b1) (a2,b2) = (sup a1 a2, sup b1 b2)

instance (LowerBounded a, LowerBounded b) => LowerBounded (a,b) where
    lowerBound = (lowerBound,lowerBound)

instance (UpperBounded a, UpperBounded b) => UpperBounded (a,b) where
    upperBound = (upperBound,upperBound)

instance (Complemented a, Complemented b) => Complemented (a,b) where
    not (a,b) = (not a, not b)

--------------------

instance Poset () where
    inf _ _ = ()

instance Lattice () where
    sup _ _ = ()

instance LowerBounded () where
    lowerBound = ()

instance UpperBounded () where
    upperBound = ()

instance Complemented () where
    not _ = ()

instance Heyting () where
    (==>) = modusPonens

--------------------------------------------------------------------------------

newtype NonNegative a = NonNegative a
    deriving Show

instance Poset a => Poset (NonNegative a) where
    inf (NonNegative a1) (NonNegative a2) = NonNegative $ inf a1 a2

instance Lattice a => Lattice (NonNegative a) where
    sup (NonNegative a1) (NonNegative a2) = NonNegative $ sup a1 a2

instance (Num a, Poset a) => LowerBounded (NonNegative a) where
    lowerBound = NonNegative 0

--------------------

newtype Discrete a = Discrete a
    deriving Show

instance Poset a => Poset (Discrete a) where
    inf (Discrete a1) (Discrete a2) = Discrete $ inf a1 a2

instance Lattice a => Lattice (Discrete a) where
    sup (Discrete a1) (Discrete a2) = Discrete $ sup a1 a2

instance LowerBounded a => LowerBounded (Discrete a) where
    lowerBound = Discrete lowerBound

--------------------------------------------------------------------------------

data HList (xs :: [a]) where
    HNil  :: HList '[]
    HCons :: a -> HList xs -> HList (a ': xs)

instance Poset (HList '[]) where
    inf _ _ = HNil

instance (Poset x, Poset (HList xs)) => Poset (HList (x ': xs)) where
    inf (x1 `HCons` xs1) (x2 `HCons` xs2) = inf x1 x2 `HCons` inf xs1 xs2

instance LowerBounded (HList '[]) where
    lowerBound = HNil

instance (LowerBounded x, LowerBounded (HList xs)) => LowerBounded (HList (x ': xs)) where
    lowerBound = lowerBound `HCons` lowerBound

instance Lattice (HList '[]) where
    sup _ _ = HNil

instance (Lattice x, Lattice (HList xs)) => Lattice (HList (x ': xs)) where
    sup (x1 `HCons` xs1) (x2 `HCons` xs2) = sup x1 x2 `HCons` sup xs1 xs2

