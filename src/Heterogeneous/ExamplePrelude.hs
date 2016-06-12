{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}

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

-- pattern Expr_negate :: forall t alg a.
--     ( View Num '[] alg t
--     ) => Free (Sig alg) t a
--       -> Free (Sig alg) t a
-- pattern Expr_negate e <- Free (unsafeExtractSigTag0 -> Sig_negate e) where
--     Expr_negate e = Free $ embedSig $ Sig_negate e

-- pattern Expr_log :: forall t alg a.
--     ( View Floating '[] alg t
--     ) => Free (Sig alg) t a
--       -> Free (Sig alg) t a
-- pattern Expr_log e <- Free ((unsafeExtractSig :: Sig alg      t   (Free (Sig alg) t a)
--                                               -> Sig Floating '[] (Free (Sig alg) t a)
--                             ) -> Sig_log e) where
-- -- pattern Expr_log e <- Free (unsafeExtractSig -> Sig_log e) --where
--     Expr_log e = Free $ embedSig $ Sig_log e

--------------------------------------------------------------------------------

type family Scalar a
mkAT ''Scalar

type instance Scalar Double = Double
type instance Scalar Var = Var

scalar1 :: AST alg '[TScalar] Var
scalar1 = Pure $ Var "scalar1"

type instance Scalar Float = Float
type instance Scalar (Free (Sig alg) t a) = Free (Sig alg) (TScalar ': t) a

----------------------------------------

class (Num a, Floating (Scalar a)) => Vector a where
    (.*) :: Scalar a -> a -> a

-- instance FAlgebra Vector where
--     data Sig Vector t a where
--         Sig_Vector_Num :: Sig Num t a -> Sig Vector t a
--         Sig_Vector_Floating_Scalar :: Sig Floating t a -> Sig Vector (TScalar ': t) a
--         Sig_dotmul :: Scalar a -> a -> Sig Vector '[] a
--
-- instance
--     ( Show a
--     , Show (Scalar a)
--     ) => Show (Sig Vector t a)
--         where
--     show (Sig_Vector_Num s) = show s
--     show (Sig_Vector_Floating_Scalar s) = show s
--     show (Sig_dotmul s a) = show s++".*"++show a

-- instance {-#OVERLAPS#-} Show (Sig Vector (t0 ': t1 ': t) a) where
--     show _ = "<<overlaps>>"

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

instance Floating a => Vector (Vec3 a) where
    (.*) s (Vec3 a1 a2 a3) = Vec3 (s*a1) (s*a2) (s*a3)

instance Floating a => Hilbert (Vec3 a) where
    dotProduct (Vec3 a1 a2 a3) (Vec3 b1 b2 b3) = a1*b1+a2*b2+a3*b3

--------------------------------------------------------------------------------

logexpAST1 :: AST Floating '[] a -> AST Floating '[] a
logexpAST1 (Free0 (Sig_log (Free0 (Sig_exp a)))) = a

-- logexpAST2 :: forall t alg a. View Floating t alg '[] => AST alg '[] a -> AST alg '[] a
-- logexpAST2 (Free (unsafeExtractSig -> Sig_log a)) = a
-- logexpAST2 (Free (unsafeExtractSig :: Sig alg      t   (Free (Sig alg) t a)
--                                    -> Sig Floating '[] (Free (Sig alg) t a)
--                             ) -> Sig_log e) = e
-- logexpAST2 (Free (unsafeExtractSig -> Sig_log
--            (Free (unsafeExtractSig -> Sig_exp a)))) = a

logexpAST4 :: View Floating '[] alg t => AST alg t a -> AST alg t a
logexpAST4 (AST_log (AST_exp a)) = a
-- logexpAST4 (Free f) = Free $ fmap logexpAST4 f
-- logexpAST4 (Pure a) = Pure a

-- logexpAST5 :: forall alg t a. View Floating '[] alg t => AST alg t a -> AST alg t a
-- logexpAST5 e = go (Proxy::Proxy '[]) (Proxy::Proxy (AST alg t a)) (Proxy::Proxy (AST alg t a)) e
--     where
--         go :: View Floating '[] alg (s++t)
--            => Proxy s
--            -> Proxy (AST alg t a)
--            -> Proxy (AST alg t a)
--            -> (AST alg (s++t) a)
--            -> (AST alg (s++t) a)
--         go _ _ _ (AST_log (AST_exp a)) = a
--         go _ _ _ (Free f) = Free $ fmapTag' go f

logexpAST5 :: View Floating '[] alg t => AST alg t a -> AST alg t a
logexpAST5 (AST_log (AST_exp a)) = a
-- logexpAST5 (Free1 f) = Free1 $ fmapAST1 logexpAST4 f
logexpAST5 (Free0 f) = Free0 $ fmapAST0 logexpAST4 f
logexpAST5 (Pure  a) = Pure a

fmapAST1 :: (forall s. View Floating '[] alg s => AST alg s a -> AST alg s a) -> Sig alg t (AST alg t a) -> Sig alg t (AST alg t a)
fmapAST1 f = undefined

fmapAST0 :: (forall s. View Floating '[] alg s => AST alg s a -> AST alg s a) -> Sig alg t (AST alg t a) -> Sig alg t (AST alg t a)
fmapAST0 f = undefined

--     fmapTag' :: Proxy s -> Proxy a -> Proxy b -> App s a -> App s b

stabAST :: AST FloatingOrd '[] a -> AST FloatingOrd '[] a
stabAST
    (AST_log
        (AST_div
            (AST_fromInteger 1)
            (AST_plus
                (AST_fromInteger 1)
                (AST_exp
                    (AST_negate x)
                )
            )
        )
    )
    = logLogistic2 x

logLogistic1 :: Floating x => x -> x
logLogistic1 x = log(1/(1+exp(-x)))

logLogistic2 :: FloatingOrd x => x -> x
logLogistic2 x = m+log(1/(exp(m)+exp(-x+m)))
    where
        m = min 0 x

logLoss :: Hilbert x => x -> x -> Scalar x
logLoss x1 x2 = logLogistic1 (dotProduct x1 x2)
