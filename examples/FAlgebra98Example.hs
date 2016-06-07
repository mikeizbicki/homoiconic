{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module HomFAlgebraExample
    where

import Prelude hiding (Monoid (..),(-),(+),negate,(==))
import Data.Foldable
import Data.List
import Data.Typeable
import Data.Proxy
import qualified Prelude as P
-- import GHC.Exts

import FAlgebra98
import Spatial98
import Topology
import Lattice

--------------------------------------------------------------------------------

class Semigroup a where
    (+) :: a -> a -> a

mkHomFAlgebra ''Semigroup

instance HomVariety Semigroup where
    laws = [ Law
        { lawName = "associative"
        , lhs = (var1+var2)+var3
        , rhs = var1+(var2+var3)
        } ]

instance Semigroup Int where (+) = (P.+)
instance Semigroup Float where (+) = (P.+)

instance Approximate98 Semigroup Float where
    epsLaws =
        [ EpsLaw
            { epsLawName = "associative"
            , epsilon = lowerBound
            }
        ]

-- instance HomFAlgebra Semigroup where
--     data Sig98 Semigroup a where
--         Sig98_plus :: a -> a -> Sig98 Semigroup a
--     runSig98 (Sig98_plus a1 a2) = a1+a2
--
-- instance Prelude.Functor (Sig98 Semigroup) where
--     fmap f (Sig98_plus a1 a2) = Sig98_plus (f a1) (f a2)

-- instance Foldable (Sig98 Semigroup) where
--     foldr f b (Sig98_plus a1 a2) = f a2 (f a1 b)

-- instance Show a => Show (Sig98 Semigroup a) where
--     show (Sig98_plus a1 a2) = show a1++"+"++show a2

-- pattern HomAST_plus ::
--     ( View98 Semigroup alg
--     ) => HomAST alg e
--       -> HomAST alg e
--       -> HomAST alg e
-- pattern HomAST_plus e1 e2 <- Free98 (unsafeExtractSig -> Sig98_plus e1 e2) where
--     HomAST_plus e1 e2 = Free98 $ embedSig $ Sig98_plus e1 e2

-- instance View98 Semigroup alg => Semigroup (Free98 (Sig98 alg) a) where
--     (+) e1 e2 = Free98 $ embedSig $ Sig98_plus e1 e2
--     (+) = HomAST_plus

--------------------

class Semigroup a => Monoid a where
    zero :: a

mkHomFAlgebra ''Monoid

instance HomVariety Monoid where
    laws =
        [ Law
            { lawName = "identity-left"
            , lhs = zero+var1
            , rhs = var1
            }
        , Law
            { lawName = "identity-right"
            , lhs = var1+zero
            , rhs = var1
            }
        ]

instance Monoid Int where zero = 0
instance Monoid Float where zero = 0

-- instance HomFAlgebra Monoid where
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

mkHomFAlgebra ''Cancellative

instance HomVariety Cancellative where
    laws =
        [ Law
            { lawName = "cancellation-right"
            , lhs = var1+var2-var2
            , rhs = var1
            }
        , Law
            { lawName = "cancellation-left"
            , lhs = var1+var2-var1
            , rhs = var2
            }
        ]

instance Cancellative Int where (-) = (P.-)
instance Cancellative Float where (-) = (P.-)

--------------------

class (Cancellative a, Monoid a) => Group a where
    negate :: a -> a
    negate a = zero - a

mkHomFAlgebra ''Group

instance HomVariety Group where
    laws =
        [ Law
            { lawName = "defn-negate"
            , lhs = negate var1
            , rhs = zero - var1
            }
        , Law
            { lawName = "inverse-left"
            , lhs = negate var1 + var1
            , rhs = zero
            }
        , Law
            { lawName = "inverse-right"
            , lhs = var1 + negate var1
            , rhs = zero
            }
        ]

instance Group Int where negate = P.negate
instance Group Float where negate = P.negate

-- instance View98 Semigroup Group where
--     embedSig s = Sig98_Group_Monoid (embedSig s)
--     unsafeExtractSig (Sig98_Group_Monoid s) = unsafeExtractSig s


--------------------------------------------------------------------------------

associator :: Group a => a -> a -> a -> a
associator a1 a2 a3 = ((a1+a2)+a3) - (a1+(a2+a3))

class HomFAlgebra alg => ToExpr alg a where
    toExpr_ :: Int -> proxy alg -> a -> HomAST alg Var

toExpr :: ToExpr alg a => proxy alg -> a -> HomAST alg Var
toExpr = toExpr_ 0

instance {-#OVERLAPPABLE#-} HomFAlgebra alg => ToExpr alg a where
    toExpr_ i palg _ = (mkExprVar $ "var"++show i)

instance {-#OVERLAPS#-} ToExpr alg a => ToExpr alg (HomAST alg Var -> a) where
    toExpr_ i palg f = toExpr_ (i+1) palg $ f (mkExprVar $ "var"++show i)
