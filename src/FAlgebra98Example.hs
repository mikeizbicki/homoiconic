{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module FAlgebra98Example
    where

import Prelude hiding (Monoid (..),(-),(+),negate)
import qualified Prelude as P
import GHC.Exts

import FAlgebra98

--------------------------------------------------------------------------------

class Semigroup a where
    (+) :: a -> a -> a

mkFAlgebra98 ''Semigroup

instance Variety98 Semigroup where
    laws = [ Law
        { name = "associative"
        , lhs = (var1+var2)+var3
        , rhs = var1+(var2+var3)
        } ]

instance Semigroup Int where (+) = (P.+)

-- instance FAlgebra98 Semigroup where
--     data Sig98 Semigroup a where
--         Sig98_plus :: a -> a -> Sig98 Semigroup a
--     runSig98 (Sig98_plus a1 a2) = a1+a2
--
-- instance Prelude.Functor (Sig98 Semigroup) where
--     fmap f (Sig98_plus a1 a2) = Sig98_plus (f a1) (f a2)

-- instance Show a => Show (Sig98 Semigroup a) where
--     show (Sig98_plus a1 a2) = show a1++"+"++show a2

-- pattern Expr98_plus ::
--     ( View98 Semigroup alg
--     ) => Expr98 alg e
--       -> Expr98 alg e
--       -> Expr98 alg e
-- pattern Expr98_plus e1 e2 <- Free98 (unsafeExtractSig -> Sig98_plus e1 e2) where
--     Expr98_plus e1 e2 = Free98 $ embedSig $ Sig98_plus e1 e2

-- instance View98 Semigroup alg => Semigroup (Free98 (Sig98 alg) a) where
--     (+) e1 e2 = Free98 $ embedSig $ Sig98_plus e1 e2
--     (+) = Expr98_plus

--------------------

class Semigroup a => Monoid a where
    zero :: a

mkFAlgebra98 ''Monoid

instance Variety98 Monoid where
    laws =
        [ Law
            { name = "identity-left"
            , lhs = zero+var1
            , rhs = var1
            }
        , Law
            { name = "identity-right"
            , lhs = var1+zero
            , rhs = var1
            }
        ]

instance Monoid Int where zero = 0

-- instance FAlgebra98 Monoid where
--     data Sig98 Monoid a where
--         Sig98_Semigroup_Monoid :: Sig98 Semigroup a -> Sig98 Monoid a
--         Sig98_zero :: Sig98 Monoid a
--     runSig98 (Sig98_Semigroup_Monoid s) = runSig98 s
--     runSig98 Sig98_zero = zero
--
-- instance Prelude.Functor (Sig98 Monoid) where
--     fmap f (Sig98_Semigroup_Monoid s) = Sig98_Semigroup_Monoid $ fmap f s
--     fmap f Sig98_zero = Sig98_zero

-- instance Show a => Show (Sig98 Monoid a) where
--     show (Sig98_Monoid_Semigroup s) = show s
--     show Sig98_zero = "zero"

-- instance View98 Semigroup Monoid where
--     embedSig = Sig98_Monoid_Semigroup
--     unsafeExtractSig (Sig98_Monoid_Semigroup s) = s

-- instance (View98 Semigroup alg, View98 Monoid alg) => Monoid (Free98 (Sig98 alg) a) where
--     zero = Free98 $ embedSig $ Sig98_zero

--------------------

class Semigroup a => Cancellative a where
    (-) :: a -> a -> a

mkFAlgebra98 ''Cancellative

instance Variety98 Cancellative where
    laws =
        [ Law
            { name = "cancellation-right"
            , lhs = var1+var2-var2
            , rhs = var1
            }
        , Law
            { name = "cancellation-left"
            , lhs = var1+var2-var1
            , rhs = var2
            }
        ]

instance Cancellative Int where (-) = (P.-)

--------------------

class (Cancellative a, Monoid a) => Group a where
    negate :: a -> a
    negate a = zero - a

mkFAlgebra98 ''Group

instance Variety98 Group where
    laws =
        [ Law
            { name = "defn-negate"
            , lhs = negate var1
            , rhs = zero - var1
            }
        , Law
            { name = "inverse-left"
            , lhs = negate var1 + var1
            , rhs = zero
            }
        , Law
            { name = "inverse-right"
            , lhs = var1 + negate var1
            , rhs = zero
            }
        ]

instance Group Int where negate = P.negate

-- instance View98 Semigroup Group where
--     embedSig s = Sig98_Group_Monoid (embedSig s)
--     unsafeExtractSig (Sig98_Group_Monoid s) = unsafeExtractSig s

