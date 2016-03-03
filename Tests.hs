{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DefaultSignatures #-}

module Tests
    ( Lawful (..)
    , Approximate (..)
    , Testable
    , isLawful
    )
    where

import qualified Prelude as P
import LocalPrelude
import Lattice
import Union
import Topology1 hiding (Lawful (..), Semigroup (..), isLawful)

import Data.Typeable
import Test.SmallCheck.Series
import Test.Tasty
import Test.Tasty.Ingredients.Basic
import qualified Test.Tasty.SmallCheck as SC
import qualified Test.Tasty.QuickCheck as QC
import Test.QuickCheck hiding (Testable)

import Debug.Trace

--------------------------------------------------------------------------------

type Testable p = (Show p, Arbitrary p, CoArbitrary p, Serial IO p, Typeable p)

--------------------

class Lawful (cxt :: * -> Constraint) (law::Symbol) where

    type LawInput cxt law a :: Type
    law :: cxt a => Proxy cxt -> Proxy law -> Proxy a -> LawInput cxt law a -> Logic a
    law _ _ _ _ = lowerBound

class
    ( Testable (LawInput cxt law a)
    , cxt a
    , Lawful cxt law
    ) => Approximate cxt law a
        where
    maxError :: Proxy cxt -> Proxy law -> Proxy a -> LawInput cxt law a -> Neighborhood a

instance {-# OVERLAPPABLE #-} (Testable (LawInput cxt law a), Topology a, cxt a, Lawful cxt law) => Approximate cxt law a where
    maxError _ _ _ _ = lowerBound

instance {-# OVERLAPS #-}
    ( Approximate cxt law a
    , Approximate cxt law b
    , Testable (LawInput cxt law (a,b))
    , cxt (a,b)
    , Splittable (LawInput cxt law (a,b)) (LawInput cxt law a) (LawInput cxt law b)
    ) => Approximate cxt law (a,b)
        where
    maxError pcxt plaw _ x =
        ( maxError pcxt plaw (Proxy::Proxy a) xa
        , maxError pcxt plaw (Proxy::Proxy b) xb
        )
        where
            (xa,xb) = split x

class Splittable a b c | a -> b c where
    split :: a -> (b,c)

instance Splittable
    ((a1,b1),(a2,b2))
    (a1,a2)
    (b1,b2)
        where
    split ((a1,b1),(a2,b2))
        = ((a1,a2),(b1,b2))

instance Splittable
    ((a1,b1),(a2,b2),(a3,b3))
    (a1,a2,a3)
    (b1,b2,b3)
        where
    split ((a1,b1),(a2,b2),(a3,b3))
        = ((a1,a2,a3),(b1,b2,b3))

instance Splittable
    ((a1,b1),(a2,b2),(a3,b3),(a4,b4))
    (a1,a2,a3,a4)
    (b1,b2,b3,b4)
        where
    split ((a1,b1),(a2,b2),(a3,b3),(a4,b4))
        = ((a1,a2,a3,a4),(b1,b2,b3,b4))

instance Splittable
    ((a1,b1),(a2,b2),(a3,b3),(a4,b4),(a5,b5))
    (a1,a2,a3,a4,a5)
    (b1,b2,b3,b4,b5)
        where
    split ((a1,b1),(a2,b2),(a3,b3),(a4,b4),(a5,b5))
        = ((a1,a2,a3,a4,a5),(b1,b2,b3,b4,b5))

instance Splittable
    ((a1,b1),(a2,b2),(a3,b3),(a4,b4),(a5,b5),(a6,b6))
    (a1,a2,a3,a4,a5,a6)
    (b1,b2,b3,b4,b5,b6)
        where
    split ((a1,b1),(a2,b2),(a3,b3),(a4,b4),(a5,b5),(a6,b6))
        = ((a1,a2,a3,a4,a5,a6),(b1,b2,b3,b4,b5,b6))

--------------------------------------------------------------------------------

isLawful :: forall cxt law a.
    ( Approximate cxt law a
    ) => Proxy cxt
      -> Proxy law
      -> Proxy a
      -> IO ()
isLawful pcxt plaw pa = defaultMain
    $ localOption (QC.QuickCheckTests 100)
    $ localOption (SC.SmallCheckDepth 3)
    $ testGroup "isLaw"
        [ QC.testProperty ("quickcheck") (\p -> law pcxt plaw pa p (maxError pcxt plaw pa p))
        ]
