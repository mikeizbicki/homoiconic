{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module HomPrelude
    where

import FAlgebra98
import Spatial98
import Prelude
import Data.Kind
import Unsafe.Coerce


mkFAlgebra ''Num
mkFAlgebra ''Fractional
mkFAlgebra ''Floating
-- mkFAlgebra ''Eq
instance FAlgebra Eq
instance Functor (Sig Eq)
instance Foldable (Sig Eq)
instance Show (Sig Eq a)
instance Eq (Sig Eq a)
mkFAlgebra ''Ord

class (Floating a, Ord a) => FloatingOrd a
instance {-#OVERLAPPABLE#-} (Floating a, Ord a) => FloatingOrd a
mkFAlgebra ''FloatingOrd

-- type family DefaultAST a :: Type->Constraint
-- type instance DefaultAST Double = Floating
-- type instance DefaultAST Float  = Floating
-- type instance DefaultAST (a -> b) = DefaultAST b
-- type instance DefaultAST Int    = Num
--
-- type AST a = AST (DefaultAST a) a

-- expLogLogistic1 :: Double -> Double
-- expLogLogistic1 x = runHomAST $ logexpAST4 $ exp $ log $ 1/(1+exp(-Pure x))
--
-- expLogLogistic2 :: Double -> Double
-- expLogLogistic2 x = 1/(1+exp(-x))

associator :: Num a => a -> a -> a -> a
associator a1 a2 a3
    = ((a1+a2)+a3) - (a1+(a2+a3))

--------------------------------------------------------------------------------

toAST1
    :: ( AST alg x -> y)
    -> (         x -> y)
toAST1 f x1 = f (Pure x1)

transform1 :: forall alg x.
    ( FAlgebra alg
    , alg x
    ) => (AST alg x -> AST alg x)
      -> (AST alg x -> AST alg x)
      -> (x -> x)
transform1 go f x = runHomAST $ go $ f (Pure x)

--------------------

toAST2
    :: ( AST alg x -> AST alg x -> y)
    -> (         x ->         x -> y)
toAST2 f x1 x2 = f (Pure x1) (Pure x2)

transform2 :: forall alg x.
    ( FAlgebra alg
    , alg x
    , alg (AST alg x)
    ) => (AST alg x -> AST alg x)
      -> (AST alg x -> AST alg x -> AST alg x)
      -> (x -> x -> x)
transform2 go f x1 x2 = runHomAST $ go $ toAST2 (f :: AST alg x -> AST alg x -> AST alg x) x1 x2

--------------------------------------------------------------------------------

logexpAST1 :: AST Floating a -> AST Floating a
logexpAST1 (Free (Sig_log (Free (Sig_exp a)))) = a

logexpAST2 :: View Floating alg => AST alg a -> AST alg a
logexpAST2 (Free (unsafeExtractSig -> Sig_log
           (Free (unsafeExtractSig -> Sig_exp a)))) = a

-- pattern AST_log ::
--     ( View Floating alg
--     ) => AST alg a -> AST alg a
-- pattern AST_log e <- Free (unsafeExtractSig -> Sig_log e) where
--     AST_log e = Free (embedSig (Sig_log e))
--
-- pattern AST_exp ::
--     ( View Floating alg
--     ) => AST alg a -> AST alg a
-- pattern AST_exp e <- Free (unsafeExtractSig -> Sig_exp e) where
--     AST_exp e = Free (embedSig (Sig_exp e))

logexpAST3 :: View Floating alg => AST alg a -> AST alg a
logexpAST3 (AST_log (AST_exp a)) = a

logexpAST4 :: View Floating alg => AST alg a -> AST alg a
logexpAST4 (AST_log (AST_exp a)) = a
logexpAST4 (Free f) = Free $ fmap logexpAST4 f
logexpAST4 (Pure a) = Pure a

testFunc :: Floating a => a -> a
testFunc a = log(exp a)

-- ghci> logexpAST4 $ testFunc 2 :: AST Floating Double
-- ((fromInteger 1)+(fromInteger 2))

testFunc2 :: Floating a => a -> a
testFunc2 a = 1+exp(exp(exp(log(log(log a)))))

-- ghci> fixAST stabilizeAST (testFunc2 var1 :: AST Floating Var)
-- ((fromInteger 1)+var1)

----------------------------------------

stabAST :: Eq a => AST FloatingOrd a -> AST FloatingOrd a
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

----------------------------------------

whereTest :: AST Num a -> AST Num a
whereTest x = y+y*y
    where
        y=3*x+1

----------------------------------------

fixAST :: (Eq (Sig alg (Free (Sig alg) a)), Eq a) => (AST alg a -> AST alg a) -> AST alg a -> AST alg a
fixAST f ast = if ast==ast'
    then ast
    else fixAST f ast'
    where
        ast' = f ast

foldConstants :: View Num alg => AST alg a -> AST alg a
foldConstants (AST_plus   (AST_fromInteger a1) (AST_fromInteger a2)) = AST_fromInteger (a1+a2)
foldConstants (AST_minus  (AST_fromInteger a1) (AST_fromInteger a2)) = AST_fromInteger (a1-a2)
foldConstants (AST_mul    (AST_fromInteger a1) (AST_fromInteger a2)) = AST_fromInteger (a1*a2)
foldConstants (AST_negate (AST_fromInteger a1)) = AST_fromInteger (negate a1)
foldConstants (Free sig) = Free $ fmap foldConstants sig
foldConstants (Pure a  ) = Pure a

constExpr :: Num a => a
constExpr = 4+2*(8-2)-1

-- ghci> fixAST foldConstants constExpr
-- (fromInteger 18)

constFunc :: Num a => a -> a -> a
constFunc x1 x2 = x1*2-(7-2)*x2

-- ghci> fixAST foldConstants (constFunc 2 3)
-- (fromInteger -11)
-- ghci> fixAST foldConstants (constFunc var1 var2)
-- ((var1*(fromInteger 2))-((fromInteger 5)*var2))

--------------------------------------------------------------------------------

data Vec3 a = Vec3 a a a

instance Num a => Num (Vec3 a) where
    (Vec3 a1 a2 a3)+(Vec3 b1 b2 b3) = Vec3 (a1+b1) (a2+b2) (a3+b3)
    (Vec3 a1 a2 a3)-(Vec3 b1 b2 b3) = Vec3 (a1-b1) (a2-b2) (a3-b3)
    (Vec3 a1 a2 a3)*(Vec3 b1 b2 b3) = Vec3 (a1*b1) (a2*b2) (a3*b3)

instance Approximate Num a => Approximate Num (Vec3 a)

--------------------------------------------------------------------------------

data Matrix a = Matrix a a a a

instance Num a => Num (Matrix a) where
    (Matrix a1 b1 c1 d1)+(Matrix a2 b2 c2 d2)
        =Matrix (a1+a2) (b1+b2) (c1+c2) (d1+d2)

    (Matrix a1 b1 c1 d1)-(Matrix a2 b2 c2 d2)
        =Matrix (a1-a2) (b1-b2) (c1-c2) (d1-d2)

    (Matrix a1 b1 c1 d1)*(Matrix a2 b2 c2 d2)
        = Matrix
            (a1*a2+b1*c2)
            (a1*b2+b1*d2)
            (c1*a2+d1*c2)
            (c1*b2+d1*d2)
