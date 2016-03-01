{-# LANGUAGE TypeInType #-}

module Union
    where

import qualified Prelude as P
import LocalPrelude
import Lattice

import GHC.TypeLits

data Union (xs :: [Type]) where
--     Union :: Proxy (n::Nat) -> Lookup n xs -> Union xs
--     Union :: Proxy (n::SNat) -> Lookup n xs -> Union xs
    Union :: Elem x xs ~ 'True => Proxy x -> x -> Union xs
--     Union :: cxt => Proxy cxt -> x -> Union xs
--     Union :: Proxy x -> x -> Union xs

data Or (xs :: [Type]) where
    OLeft :: x -> Or (x:xs)
    ORight :: Or xs -> Or (x:xs)

type family Lookup n xs where
    Lookup 0 (x ': xs) = x
    Lookup n (_ ': xs) = Lookup (n-1) xs

type family Elem (x::k) (xs::[k]) where
    Elem _ '[]       = 'False
    Elem x (x ': xs) = 'True
    Elem y (x ': xs) = Elem y xs

type family Map (x::k -> Constraint) (xs::[k]) :: Constraint where
    Map f '[] = ()
    Map f (x ': xs) = (f x, Map f xs)

-- instance Show (Union '[]) where
--     show (Union _ _) = "Union '[]"

-- instance (Show x, Show (Union xs)) => Show (Union (x:xs)) where
--     show (Union _ x) = show x

-- instance Map Show xs => Show (Union xs) where
--     show (Union _ x) = show x

-- test1 = Union (Proxy::Proxy (x~Char)) 'c' :: Union [Char,Int]
-- test2 = Union Proxy (1::Int) :: Union [Char,Int]

-- test :: Union '[Char, Int] -> String
-- test (Union _ (c::Char)) = show c
-- test (Union (Proxy::Proxy Char) (c::Char)) = show c

type family (++) (xs::[a]) (ys::[a]) where

type family (||) a b where
    Union xs || Union ys = Union (xs++ys)
    a        || Union xs = Union (a:xs)
    Union xs || b        = Union (xs++ '[b])
    a        || b        = Union '[a,b]
