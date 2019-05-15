-- the class hierarchy in this example requires no GHC extensions

-- the following GHC extensions are required for the FAlgebra
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

import Homoiconic.Homogeneous

import Prelude hiding (Monoid (..),(-),(+),negate,(==),minBound, Semigroup(..))
import qualified Prelude as P hiding (Semigroup, Monoid)

--------------------------------------------------------------------------------

class Semigroup a where
    (+) :: a -> a -> a

mkFAlgebra ''Semigroup

instance Semigroup Int where (+) = (P.+)
instance Semigroup Float where (+) = (P.+)

--------------------

class Semigroup a => Monoid a where
    zero :: a

mkFAlgebra ''Monoid

instance Monoid Int where zero = 0
instance Monoid Float where zero = 0

--------------------

class Semigroup a => Cancellative a where
    (-) :: a -> a -> a

mkFAlgebra ''Cancellative

instance Cancellative Int where (-) = (P.-)
instance Cancellative Float where (-) = (P.-)

--------------------

class (Cancellative a, Monoid a) => Group a where
    negate :: a -> a
    negate a = zero - a

mkFAlgebra ''Group

instance Group Int where negate = P.negate
instance Group Float where negate = P.negate

--------------------------------------------------------------------------------

main = do
    let x = Pure 1 :: AST Group Int
        y = Pure 2 :: AST Group Float

    let expr1 = ((x+x)-x+zero)
    putStrLn $ "expr1 = "++show expr1
    putStrLn $ "runAST expr1 = "++show (runAST expr1)

    let expr2 = y+zero+y-(negate y)+y
    putStrLn $ "expr2 = "++show expr2
    putStrLn $ "runAST expr2 = "++show (runAST expr2)

    putStrLn "done."
