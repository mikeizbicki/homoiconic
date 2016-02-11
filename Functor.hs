{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeApplications #-}

module Functor
    where

import Lattice
import LocalPrelude
import Topology2

--------------------------------------------------------------------------------

data NoType

-- type family GetCons k (f::k) = (r::k) -- | r -> k
-- type instance GetCons (Type -> Type) f      = f
-- type instance GetCons Type           [a]    = [NoType]
--
-- type family AppCons k (f::k) e :: Type
-- type instance AppCons (Type -> Type) f      e = f e
-- type instance AppCons Type           [a]    e = [e]
--
-- type SetElem k f e = AppCons k (GetCons k f) e
--
-- type family SetElem k1 (f::k1) e :: Type
-- type instance SetElem (Type -> Type) f      e = f e
-- type instance SetElem Type           [a]    e = [e]
--
-- type family GetElem k1 (f::k1) :: Type
-- type instance GetElem (Type -> Type) f      = NoType
-- type instance GetElem Type           [a]    = a

--------------------

-- class Functor k (f :: k) where
--     type SetElem k f a = r | r -> k f
--     fmap :: proxy f -> (a -> b) -> SetElem k f a -> SetElem k f b
--
-- instance Functor (Type->Type) [] where
--     type SetElem (Type->Type) [] b = [b]
--     fmap _ = map
--
-- instance Functor Type [NoType] where
--     fmap _ = map

--------------------

data Lens (a::k)

-- type family Set  (lens::k) (f::Type) (a::Type) = (r::Type) -- | r -> Set lens f NoType
-- type family Set  (lens::k) (f::Type) (a::Type) = (r::Type) | r -> lens f
type family Set  (lens::k) (f::Type) (a::Type) = (r::Type) | r -> f
type family Get  (lens::k) (f::Type)

-- type instance Set  () a b = b
-- type instance Set  () NoType b = b
type instance Get  () a   = a

-- type instance Set  (Lens k) [a]      b = [Set k a b]
-- type instance Get  (Lens k) [a]        = Get k a

type instance Set  "elem" [NoType] b = [b]
-- type instance Set  "elem" [a] b = [b]
type instance Get  "elem" [a]   = a

{- Laws:

 forall f a.        SetElem f (SetElem f a) ~ SetElem f a
 forall f a.        GetElem (SetElem f a) ~ a
 forall f a1 a2.    GetElem f (SetElem (SetElem f a1) a2) ~ a2

 forall f a1 a2.    a1 ~ a2 => f a1 ~ f a2
 forall f a1 a2.    SetElem f a1 ~ SetElem f a2 => a1~a2

 -}

class Functor (f :: Type) where
    type SetElem f a = r | r -> f

    fmap :: (a -> b) -> SetElem f a -> SetElem f b
--     fmap :: (a -> b) -> f { elem=a } -> f { elem=b }

instance Functor [Type] where
    type SetElem [Type] b = [b]
    fmap = map

-- class (Functor f, Semigroup f, Poset f) => Container f where
--     elem :: Topology a => a -> SetElem f a -> Logic a
class (Semigroup f, Poset f, Logic f~Logic (Elem f)) => Container f where
    type Elem f
    elem :: Elem f -> f -> Logic f

instance Topology a => Container [a] where
    type Elem [a] = a
    elem a (x:xs) = a==x || elem a xs
    elem a []     = lowerBound

class Functor f => Monad f where
    return :: a -> SetElem f a

    join :: SetElem f (SetElem f a) -> SetElem f a

    (>>=) ::
--         ( () => SetElem f (SetElem f b)~SetElem f b
--         , (SetElem f a~SetElem f b) => a~b
--         ) => SetElem f a -> (a -> SetElem f b) -> SetElem f b
        SetElem f a -> (a -> SetElem f b) -> SetElem f b
--     m>>=g = join (fmap g m)

instance Monad [Type] where
    return = return
    join = concat

test :: [Float]
test = fmap (+1) $ return 1 -- [1,2,3]

----------------------------------------

-- class Functor' f where
--     type Elem' f
--     fmap' :: (a -> b) -> f a -> f b

