{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeApplications #-}

module Functor2
    where

import qualified Prelude as P

import Lattice
import LocalPrelude
import Topology2

import Test.QuickCheck.Arbitrary
import GHC.Word
import qualified Data.ByteString.Lazy as BS

--------------------------------------------------------------------------------

data ByteString a where
    ByteString :: a~Word8 => BS.ByteString -> ByteString a

instance Show (ByteString Word8) where
    show (ByteString bs) = show bs

instance Arbitrary (ByteString Word8) where
    arbitrary = arbitrary P.>>= (P.return . ByteString . BS.pack)

instance Topology (ByteString Word8) where
    type Neighborhood (ByteString Word8) = ()

    isNeighbor (ByteString bs1) (ByteString bs2) _ = bs1 P.== bs2

instance Semigroup (ByteString Word8) where
    (ByteString bs1)+(ByteString bs2) = ByteString $ BS.append bs1 bs2

--------------------------------------------------------------------------------

class Functor f where
    fmap :: (a -> b) -> f a -> f b

instance Functor [] where
    fmap = map

-- instance Functor ByteString where
--     fmap f (ByteString bs) = ByteString (BS.map f bs)

----------------------------------------

class Singleton f where
    type ValidSingleton f a :: Constraint
    type ValidSingleton f a = ()
    singleton :: ValidSingleton f a => a -> f a

instance Singleton [] where
    singleton a = [a]

instance Singleton ByteString where
    type ValidSingleton ByteString a = a~Word8
    singleton = ByteString . BS.singleton

----------------------------------------

class (Singleton f, ValidSingleton f a, Semigroup (f a)) => Constructible f a where
    cons :: a -> f a -> f a
    cons a f = singleton a + f

instance Topology a => Constructible [] a where
    cons = (:)

instance Constructible ByteString Word8 where
    cons a (ByteString fa) = ByteString $ BS.cons a fa

----------------------------------------

class Foldable f where
    foldMap :: Semigroup b => (a -> b) -> f a -> b

instance Foldable [] where
--     foldMap = P.foldMap

instance Foldable ByteString where
    foldMap f (ByteString bs) = foldMap f (BS.unpack bs)

----------------------------------------

class Foldable t => Traversable t where
    traverse :: Monad f => (a -> f b) -> t a -> f (t b)
    sequence :: Monad m => t (m a) -> m (t a)

----------------------------------------

class (Functor f, Singleton f) => Monad f where
    join :: f (f a) -> f a

instance Monad [] where
    join = concat
