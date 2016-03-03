module Lattice
    where

import Prelude (fromInteger)
import qualified Prelude as P
import LocalPrelude

--------------------------------------------------------------------------------


class Poset a where
    inf :: a -> a -> a

class Poset a => Lattice a where
    sup :: a -> a -> a

class Poset a => LowerBounded a where
    lowerBound :: a

class Lattice a => UpperBounded a where
    upperBound :: a

class (LowerBounded a, UpperBounded a) => Complemented a where
    not :: a -> a

class (LowerBounded a, UpperBounded a) => Heyting a where
    infixr 3 ==>
    (==>) :: a -> a -> a

modusPonens :: Complemented b => b -> b -> b
modusPonens b1 b2 = not b1 || b2

--------------------

infixr 3 &&
(&&) :: Poset a => a -> a -> a
(&&) = inf

infixr 3 ||
(||) :: Lattice a => a -> a -> a
(||) = sup

--------------------------------------------------------------------------------

instance Poset Float where
    inf = P.min

instance Lattice Float where
    sup = P.max

instance Poset Rational where
    inf = P.min

instance Lattice Rational where
    sup = P.max

instance Poset Integer where
    inf = P.min

instance Lattice Integer where
    sup = P.max

--------------------

instance Poset Int where
    inf a1 a2 = P.min a1 a2

instance Lattice Int where
    sup a1 a2 = P.max a1 a2

--------------------

instance Poset Bool where
    inf True True = True
    inf _    _    = False

instance Lattice Bool where
    sup False False = False
    sup _     _     = True

instance LowerBounded Bool where
    lowerBound = False

instance UpperBounded Bool where
    upperBound = True

instance Complemented Bool where
    not True = False
    not False = True

instance Heyting Bool where
    (==>) = modusPonens

----------------------------------------

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

