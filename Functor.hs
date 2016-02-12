{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeApplications #-}

module Functor
    where

import qualified Prelude as P

import Lattice
import LocalPrelude
import Topology2

import qualified Data.ByteString.Lazy as BS

--------------------------------------------------------------------------------

data Lens (a::k)

type family Base (lens::k) (f::k2)           = (r::k3)
type family Set  (lens::k) (f::k2) (a::Type) = (r::Type) | r -> f
type family Get  (lens::k) (f::k2)

type family SetElem   (f::k2) (a::Type) = (r::Type) | r -> f
type instance SetElem [] b = [b]
type family BaseElem  (f::k) :: k2
type instance BaseElem [a] = [a]

-- type instance Set  () a b = b
-- type instance Set  () Type b = b
type instance Get  () a   = a

-- type instance Set  (Lens k) [a]      b = [Set k a b]
-- type instance Get  (Lens k) [a]        = Get k a

type instance Base "elem" [a] = [Type]
type instance Set  "elem" [Type] b = [b]
-- type instance Set  "elem" [a] b = [b]
type instance Get  "elem" [a]   = a


{- Laws:

 forall f a.        Set "elem" f (Set "elem" f a) ~ Set "elem" f a
 forall f a.        GetElem (Set "elem" f a) ~ a
 forall f a1 a2.    GetElem f (Set "elem" (Set "elem" f a1) a2) ~ a2

 forall f a1 a2.    a1 ~ a2 => f a1 ~ f a2
 forall f a1 a2.    Set "elem" f a1 ~ Set "elem" f a2 => a1~a2

 -}

--------------------------------------------------------------------------------

class Functor (f :: k) where
    fmap :: (a -> b) -> Set "elem" f a -> Set "elem" f b
    -- IDEA: make syntax like
    -- fmap :: (a -> b) -> f { elem=a } -> f { elem=b }

-- instance Functor [Type] where
--     type Set "elem" [Type] b = [b]
--     fmap = map

instance Functor [Type] where
    fmap = map

----------------------------------------

class Functor f => Monad f where
    return :: a -> Set "elem" f a

    join :: Set "elem" f (Set "elem" f a) -> Set "elem" f a

    (>>=) :: Set "elem" f a -> (a -> Set "elem" f b) -> Set "elem" f b
--     m>>=g = join (fmap g m)

instance Monad [Type] where
    return = return
    join = concat
--
-- instance Monad [] where
--     return = return
--     join = concat

test :: [Float]
test = fmap (+1) $ return 1 -- [1,2,3]

----------------------------------------

class IxFunctor f where
    type IndexOf i f :: Constraint
--     imap :: (i `IndexOf` f => i -> a -> b) -> Set "elem" f a -> Set "elem" f b
    imap :: (Int -> a -> b) -> Set "elem" f a -> Set "elem" f b

-- instance IxFunctor [] where
--     type IndexOf i [] = i~Int -- (Num i, Semigroup i)
--
--     imap f xs = go (0::Int) xs
--         where
--             go i []     = []
--             go i (x:xs) = f i x:go (i+1) xs

----------------------------------------

-- instance Topology Type
-- instance Semigroup Type

{- law
 - Semigroup [Type] -> forall a. Semigroup a => Semigroup [a]
 - Semigroup [] -> forall a. Semigroup [a]
 - cxt (Set "elem" f a)
 -}
type family Test f :: Constraint
-- type instance Test [a] = Functor [Type]
type instance Test a = Functor (Base "elem" a)

type Test2 f = Functor (Base "elem" f)

-- class Container f where
-- class (Poset f) => Container f where
-- class (Semigroup f, Poset f) => Container f where
-- class (Functor (Base "elem" f), Poset f) => Container f where
-- class (Test f, Poset f) => Container f where
-- class (Test (Base "elem" f), Poset f) => Container f where
-- class (Test f , Poset f) => Container f where
--     type Test3 f :: Constraint
--     type Test3 f = Functor (Base "elem" f)
class (Poset f) => Container f where
--     elem :: Topology a => a -> Set "elem" f a -> Logic a
--     elem :: a -> Set "elem" f a -> Logic a
    elem :: Get "elem" f -> f -> Logic (Get "elem" f)

instance Topology a => Container [a] where
-- instance Topology a => Container [a] where
    elem a (x:xs) = a==x || elem a xs
    elem a []     = lowerBound

-- class (Semigroup f, Poset f, Logic f~Logic (Elem f)) => Container f where
--     type Elem f
--     elem :: Elem f -> f -> Logic f

-- instance Topology a => Container [a] where
--     type Elem [a] = a
--     elem a (x:xs) = a==x || elem a xs
--     elem a []     = lowerBound

----------------------------------------

class Container f => Foldable f where
--     foldMap :: Semigroup b => (a -> b) -> Set "elem" f a -> b
    foldMap :: P.Monoid b => (Get "elem" f -> b) -> f -> b

instance Topology a => Foldable [a] where
    foldMap = P.foldMap

--------------------------------------------------------------------------------

class Func f where
    fm :: (a -> b) -> f a -> f b

-- class (Semigroup (f a), Func f) => Container (f a) where

