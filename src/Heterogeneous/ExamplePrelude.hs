module Heterogeneous.ExamplePrelude
    where

import Prelude hiding (Ord(..))
import Heterogeneous.FAlgebra

import Data.Proxy

--------------------------------------------------------------------------------

type instance TypeConstraints t a = ()

mkFAlgebra ''Num
mkFAlgebra ''Fractional
mkFAlgebra ''Floating
-- mkFAlgebra ''Eq
-- instance FAlgebra Eq
-- instance Functor (Sig Eq)
-- instance Foldable (Sig Eq)
-- instance Show (Sig Eq a)
-- instance Eq (Sig Eq a)
-- mkFAlgebra ''Ord

class Ord a where
    min :: a -> a -> a
    max :: a -> a -> a
mkFAlgebra ''Ord

class (Floating a, Ord a) => FloatingOrd a
instance {-#OVERLAPPABLE#-} (Floating a, Ord a) => FloatingOrd a
mkFAlgebra ''FloatingOrd

-- pattern Expr_plus ::
--     ( ViewPoset alg t
--     , TypeConstraints t a
--     ) => Free (Sig alg) t a
--       -> Free (Sig alg) t a
--       -> Free (Sig alg) t a

pattern Expr_log :: forall t alg a.
    ( View Floating '[] alg t
    ) => Free (Sig alg) t a
      -> Free (Sig alg) t a
pattern Expr_log e <- Free ((unsafeExtractSig :: Sig alg      t   (Free (Sig alg) t a)
                                              -> Sig Floating '[] (Free (Sig alg) t a)
                            ) -> Sig_log e) where
-- pattern Expr_log e <- Free (unsafeExtractSig -> Sig_log e) --where
    Expr_log e = Free $ embedSig $ Sig_log e

--------------------------------------------------------------------------------

type family Scalar a
mkAT ''Scalar

type instance Scalar Float = Float
type instance Scalar (Free (Sig alg) t a) = Free (Sig alg) (TScalar ': t) a

----------------------------------------

class (Num a, Fractional (Scalar a)) => Vector a where
    (.*) :: Scalar a -> a -> a

mkFAlgebra ''Vector

-- pattern AST_dotmul e1 e2 <- Free (unsafeExtractSig -> Sig_dotmul e1 e2) where
--     AST_dotmul e1 e2 = Free $ embedSig $ Sig_dotmul e1 e2

--------------------------------------------------------------------------------

class Vector a => Hilbert a where
    dotProduct :: a -> a -> Scalar a

mkFAlgebra ''Hilbert

-- pattern AST_dotProduct :: forall alg t a.
--     ( View Hilbert '[TScalar] alg (TScalar ': t)
--     ) => Free (Sig alg) t a
--       -> Free (Sig alg) t a
--       -> Free (Sig alg) (TScalar ': t) a
-- pattern AST_dotProduct e1 e2 <- FreeTag (unsafeExtractSigTag -> Sig_dotProduct e1 e2) where
--     AST_dotProduct e1 e2 = FreeTag $ embedSigTag $ Sig_dotProduct e1 e2

--------------------------------------------------------------------------------

data Vec3 a = Vec3 a a a
    deriving (Eq,Show)

type instance Scalar (Vec3 a) = a

instance Num a => Num (Vec3 a) where
    (+) (Vec3 a1 a2 a3) (Vec3 b1 b2 b3) = Vec3 (a1+b1) (a2+b2) (a3+b3)
    (-) (Vec3 a1 a2 a3) (Vec3 b1 b2 b3) = Vec3 (a1-b1) (a2-b2) (a3-b3)
    (*) (Vec3 a1 a2 a3) (Vec3 b1 b2 b3) = Vec3 (a1*b1) (a2*b2) (a3*b3)
    signum (Vec3 a1 a2 a3) = Vec3 (signum a1) (signum a2) (signum a3)
    abs (Vec3 a1 a2 a3) = Vec3 (abs a1) (abs a2) (abs a3)
    fromInteger i = Vec3 (fromInteger i) (fromInteger i) (fromInteger i)

instance Fractional a => Vector (Vec3 a) where
    (.*) s (Vec3 a1 a2 a3) = Vec3 (s*a1) (s*a2) (s*a3)

--------------------------------------------------------------------------------

logexpAST1 :: AST Floating '[] a -> AST Floating '[] a
logexpAST1 (Free (Sig_log (Free (Sig_exp a)))) = a

-- logexpAST2 :: forall t alg a. View Floating t alg '[] => AST alg '[] a -> AST alg '[] a
-- logexpAST2 (Free (unsafeExtractSig -> Sig_log a)) = a
-- logexpAST2 (Free (unsafeExtractSig :: Sig alg      t   (Free (Sig alg) t a)
--                                    -> Sig Floating '[] (Free (Sig alg) t a)
--                             ) -> Sig_log e) = e
-- logexpAST2 (Free (unsafeExtractSig -> Sig_log
--            (Free (unsafeExtractSig -> Sig_exp a)))) = a

logexpAST4 :: View Floating '[] alg '[] => AST alg '[] a -> AST alg '[] a
-- logexpAST4 :: AST alg '[] a -> AST alg '[] a
logexpAST4 (Expr_log a) = a
-- logexpAST4 (AST_log (AST_exp a)) = a
-- logexpAST4 (Free f) = Free $ fmap logexpAST4 f
-- logexpAST4 (Pure a) = Pure a

-- stabAST :: Eq a => AST FloatingOrd '[] a -> AST FloatingOrd '[] a
-- stabAST
--     (AST_log
--         (AST_div
--             (AST_fromInteger 1)
--             (AST_plus
--                 (AST_fromInteger 1)
--                 (AST_exp
--                     (AST_negate x)
--                 )
--             )
--         )
--     )
--     = logLogistic2 x

logLogistic1 :: Floating x => x -> x
logLogistic1 x = log(1/(1+exp(-x)))

logLogistic2 :: FloatingOrd x => x -> x
logLogistic2 x = m+log(1/(exp(m)+exp(-x+m)))
    where
        m = min 0 x
