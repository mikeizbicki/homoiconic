{-# LANGUAGE UndecidableSuperClasses #-}

module Algebra3
    where

import qualified Prelude as P
import LocalPrelude hiding ((.))
import Lattice
import Tests
import Topology1 hiding (Lawful (..), Semigroup (..), isLawful)
-- import Union
import Category

import Test.SmallCheck.Series hiding (NonNegative)
import Test.Tasty
import qualified Test.Tasty.SmallCheck as SC
import qualified Test.Tasty.QuickCheck as QC
import Test.QuickCheck hiding (Testable,NonNegative)

import Debug.Trace
import GHC.Generics

-------------------------------------------------------------------------------

data AT
    = Id
    | Scalar
    | AppAT AT AT

type family AppAT (t::AT) (a::Type)
type instance AppAT 'Id a = a
type instance AppAT 'Scalar a = Scalar a
type instance AppAT ('AppAT t t') a = AppAT t (AppAT t' a)

{-
type family UnwrapAT a where
    UnwrapAT (WrapAT t a) = a
    UnwrapAT a = a

--------------------

newtype WrapAT (t::AT) (a::Type) = WrapAT (AppAT t a)

instance Show a => Show (WrapAT 'Id a) where
    show (WrapAT a) = "(WrapAT 'Id "++show a++")"

instance Show (Scalar a) => Show (WrapAT 'Scalar a) where
    show (WrapAT a) = "(WrapAT 'Scalar "++show a++")"

instance Num a => Num (WrapAT 'Id a) where
    fromInteger n = WrapAT $ fromInteger n

instance Num (Scalar a) => Num (WrapAT 'Scalar a) where
    fromInteger n = WrapAT $ fromInteger n

----------------------------------------

data Free f e = Free (f (Free f e)) | Pure e

type instance Scalar (Free f e) = Free f (Scalar e)

instance (Show e, Show (f (Free f e))) => Show (Free f e) where
    show (Pure e) = show e
    show (Free f) = show f

instance (Num a) => Num (Free f a) where
    fromInteger n = Pure $ fromInteger n

----------------------------------------

-- type Expr cxt = Free (FExpr cxt)

----------------------------------------

class FAlgebra (cxt :: Type -> Constraint) where
    data FExpr cxt (t::AT) (a::Type)
    runFExpr :: cxt (AppAT t a) => FExpr cxt t a -> AppAT t a

-------------------------------------------------------------------------------
-}

class Semigroup a where
    (+) :: a -> a -> a

instance Semigroup Int where (+) = (P.+)

-- instance FAlgebra Semigroup where
--     data FExpr Semigroup t a where
--         FExpr_plus
--             :: AppAT t a
--             -> AppAT t a
--             -> FExpr Semigroup t a
--     runFExpr (FExpr_plus a1 a2) = a1+a2
--
-- instance
--     ( AppAT t (Free (FExpr Semigroup t) a)
--     ~         (Free (FExpr Semigroup t) a)
--     ) => Semigroup (Free (FExpr Semigroup t) a) where
--     e1+e2 = Free $ FExpr_plus e1 e2

----------------------------------------

class (Scalar (Scalar a)~Scalar a, Module (Scalar a), Semigroup a) => Module a where
    (.*) :: a -> Scalar a -> a

instance Module Int where (.*) = (P.*)

-- instance FAlgebra Module where
--     data FExpr Module a where
--         FExpr_Module
--             :: {-#UNPACK#-}!(FExpr Semigroup a)
--             -> FExpr Module a
--         FExpr_mul
--             :: a
--             -> Scalar a
--             -> FExpr Module (WrapAT 'Id a)
--
--     runFExpr (FExpr_Module e) = runFExpr e
--     runFExpr (FExpr_mul a sa) = WrapAT $ a .* sa

----------------------------------------

class Module a => Hilbert a where
    (<>) :: a -> a -> Scalar a

instance Hilbert Int where (<>) = (P.*)

-- instance FAlgebra Hilbert where
--     data FExpr Hilbert a where
--         FExpr_Hilbert
--             :: {-#UNPACK#-}!(FExpr Module a)
--             -> FExpr Hilbert a
--         FExpr_dp
--             :: a
--             -> a
--             -> FExpr Hilbert (WrapAT 'Scalar a)
--
--     runFExpr (FExpr_Hilbert e) = runFExpr e
--     runFExpr (FExpr_dp a1 a2) = WrapAT $ a1<>a2

type instance Scalar Int = Int

--------------------------------------------------------------------------------

data Free f (t::AT) e = Free (f (Free f t e)) | Pure (AppAT t e)

-- type instance Scalar (Free f t e) = Free f ('AppAT 'Scalar t) e
type instance Scalar (Free f t e) = Free f t (Scalar e)

instance (Show (AppAT t e), Show (f (Free f t e))) => Show (Free f t e) where
    show (Pure e) = show e
    show (Free f) = show f

instance (Num (AppAT t a)) => Num (Free f t a) where
    fromInteger n = Pure $ fromInteger n

type Expr t a = Free (FEx t) t a

----------------------------------------

data FEx (t::AT) (a::Type) where
    FEx_plus :: Semigroup (AppAT t a) => AppAT t a -> AppAT t a                 -> FEx t a
    FEx_mul  :: Module    (AppAT t a) => AppAT t a -> AppAT 'Scalar (AppAT t a) -> FEx t a
    FEx_dp   :: Hilbert   (AppAT t a) => AppAT t a -> AppAT t a                 -> FEx ('AppAT 'Scalar t) a

instance
    ( Show (AppAT t a)
    , Show (Scalar (AppAT t a))
    ) => Show (FEx t a) where
    show (FEx_plus a1 a2) = "("++show a1++"+"++show a2++")"
    show (FEx_mul  a1 a2) = "("++show a1++".*"++show a2++")"

instance {-#OVERLAPS#-}
    ( Show (AppAT t a)
    , Show (Scalar (AppAT t a))
    , Scalar (Scalar (AppAT t a)) ~ Scalar (AppAT t a)
    ) => Show (FEx ('AppAT 'Scalar t) a)
        where
    show (FEx_plus a1 a2) = "("++show a1++"+"++show a2++")"
    show (FEx_mul  a1 a2) = "("++show a1++".*"++show a2++")"
    show (FEx_dp   a1 a2) = "("++show a1++"<>"++show a2++")"

instance
    ( AppAT t (Free (FEx t) t a)
    ~         (Free (FEx t) t a)
    ) => Semigroup (Free (FEx t) t a)
        where
    e1+e2 = Free $ FEx_plus e1 e2

instance
    ( AppAT t (Free (FEx t) t a)
    ~         (Free (FEx t) t a)
    , AppAT t (Expr t (Scalar a))
    ~         (Expr t (Scalar a))
    , Scalar (Scalar a)~Scalar a
    ) => Module (Free (FEx t) t a)
        where
    e1.*e2 = Free $ FEx_mul e1 e2

instance
    ( Scalar ( AppAT t (Expr ('AppAT 'Scalar t) a) )
    ~                  (Expr ('AppAT 'Scalar t) a)
    , AppAT t (Expr ('AppAT 'Scalar t) (Scalar a))
    ~         (Expr ('AppAT 'Scalar t) a)
    , Scalar (Scalar a)~Scalar a
    ) => Hilbert (Expr ('AppAT 'Scalar t) a)
        where
    e1<>e2 = Free $ FEx_dp e1 e2

runFEx :: FEx t a -> AppAT t a
runFEx (FEx_plus a1 a2) = a1+a2
runFEx (FEx_mul  a  as) = a.*as
runFEx (FEx_dp   a1 a2) = a1<>a2

eval ::
    ( AppAT t (Free (FEx t) t a)
    ~         (Free (FEx t) t a)
    , AppAT t (Free (FEx t) t (Scalar a))
    ~         (Free (FEx t) t (Scalar a))
    , AppAT t (Scalar a)
    ~ Scalar (AppAT t a)
    , Scalar (Scalar a) ~ Scalar a
    , Scalar (Scalar (AppAT t a)) ~ Scalar (AppAT t a)
    , Semigroup (AppAT t a)
    , Module (AppAT t a)
    ) => Free (FEx t) t a -> AppAT t a
eval (Pure e) = e
eval (Free (FEx_plus e1 e2)) = eval e1+ eval e2
eval (Free (FEx_mul  e1 e2)) = eval e1.*eval e2
-- eval (Free (FEx_dp   e1 e2)) = eval e1<>eval e2

-- eval' ::
--     ( AppAT ('AppAT 'Scalar t) (Expr ('AppAT 'Scalar t) a)
--     ~         (Expr ('AppAT 'Scalar t) a)
--     , AppAT ('AppAT 'Scalar t) (Expr ('AppAT 'Scalar t) (Scalar a))
--     ~         (Expr ('AppAT 'Scalar t) (Scalar a))
--     , AppAT ('AppAT 'Scalar t) (Scalar a)
--     ~ Scalar (AppAT ('AppAT 'Scalar t) a)
--     , Scalar (Scalar a) ~ Scalar a
--     , Scalar (Scalar (AppAT ('AppAT 'Scalar t) a)) ~ Scalar (AppAT ('AppAT 'Scalar t) a)
--     , Semigroup (AppAT ('AppAT 'Scalar t) a)
--     , Module (AppAT ('AppAT 'Scalar t) a)
--     ) => Expr ('AppAT 'Scalar t) a -> AppAT ('AppAT 'Scalar t) a
-- eval' (Pure e) = e
-- eval' (Free (FEx_plus e1 e2)) = eval' e1+ eval' e2
-- eval' (Free (FEx_mul  e1 e2)) = eval' e1.*eval' e2
-- eval' (Free (FEx_dp   e1 e2)) = eval e1 -- eval' e1<>eval' e2
