module Normal
    where

import LocalPrelude
import Algebra
import Lattice
import Topology1

--------------------------------------------------------------------------------

data Normal (cat :: Type -> Type -> Type) (elem :: Type) = Normal
    { mu    :: elem
    , sigma :: cat elem elem
    }

instance
    ( Topology elem
    , Topology (cat elem elem)
    , Neighborhood elem ~ Neighborhood (cat elem elem)
    ) => Topology (Normal cat elem)
        where
    type Neighborhood (Normal cat elem) = Neighborhood elem
    (Normal mu1 sigma1)==(Normal mu2 sigma2)
        = mu1    == mu2
       && sigma1 == sigma2

-- NOTE:
-- this assumes independence;
-- is there a better way to make the assumption explicit in the type?
instance
    ( Semigroup (cat elem elem)
    , Semigroup elem
    , Neighborhood elem ~ Neighborhood (cat elem elem)
    ) => Semigroup (Normal cat elem)
        where
    (Normal mu1 sigma1)+(Normal mu2 sigma2)
        = Normal (mu1+mu2) (sigma1+sigma2)

--------------------------------------------------------------------------------

data MLE model = MLE
    { numdp :: !(Scalar model)
    , model :: !model
    }

instance
    ( Topology (Scalar model)
    , Topology model
    , Neighborhood (Scalar model)~Neighborhood model
    ) => Topology (MLE model)
        where
    type Neighborhood (MLE model) = Neighborhood model
    (MLE numdp1 model1)==(MLE numdp2 model2)
        = numdp1==numdp2
       && model1==model2

instance
    ( Semigroup (Scalar model)
    , Semigroup model
    , Neighborhood (Scalar model)~Neighborhood model
    ) => Semigroup (MLE model)
        where
