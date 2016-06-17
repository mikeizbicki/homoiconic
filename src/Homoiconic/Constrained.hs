{-# LANGUAGE AllowAmbiguousTypes #-}

module Homoiconic.Constrained
    (
    -- * Constrained FAlgebras
      FAlgebra (..)
    , AST
    , runAST

    -- ** Dealing with Type Families
    , Tag
    , AppTag
    , AppTags
    , ConsTag

    -- ** Constrained Free Monad
    , Free (..)
    , FreeConstraints
    , MkFree (..)

    -- ** Converting between FAlgebras
    , View (..)

    -- ** Variable definitions
    , Var
    , var1
    , var2
    , var3

    -- * Template Haskell
    , mkFAlgebra
    , mkTag
    , mkTagFromCxt

    -- ** Helper functions
    , unsafeExtractSigTag0
    , unsafeExtractSigTag
    , unsafeCoerceSigTag
    , runSig1Snoc
    , runSig0Snoc
    , embedSigTag
    , Snoc

    -- ** Other need types
    , Proxy (..)
    , Typeable
    , Constraint
    )
    where

import Homoiconic.Common.Tags
import Homoiconic.Constrained.TH

import Prelude
import Control.Monad
import Data.Foldable
import Data.List
import Data.Maybe
import Data.Typeable
import Data.Proxy

import Data.Kind
import GHC.Exts hiding (IsList(..))

import Unsafe.Coerce

--------------------------------------------------------------------------------

class Typeable alg => FAlgebra (alg::Type->Constraint) where
    data Sig alg (t::[Tag]) a

    runSig1 :: alg a => proxy a -> Sig alg (s ':  t) (AppTags t a) -> AppTags (s ':  t) a
    runSig0 :: alg a => proxy a -> Sig alg        t  (AppTags t a) -> AppTags        t  a

    mapRun :: (FreeConstraints t' a)
         => (forall s. Free (Sig alg') s a -> AppTags s a)
         -> Sig alg t (Free (Sig alg') t' a)
         -> Sig alg t (AppTags t' a)

type AST (alg::Type->Constraint) t a = Free (Sig alg) t a

runAST :: forall alg t a.
    ( FAlgebra alg
    , alg a
    ) => Free (Sig alg) t a -> AppTags t a
runAST (Pure  a) = a
runAST (Free0 s) = runSig0 (Proxy::Proxy a) $ mapRun runAST s
runAST (Free1 s) = runSig1 (Proxy::Proxy a) $ mapRun runAST s

----------------------------------------

class (FAlgebra alg1, FAlgebra alg2) => View alg1 t1 alg2 t2 where
    embedSig          :: Sig alg1 t1  a -> Sig alg2 t2  a
    unsafeExtractSig  :: Sig alg2 t2  a -> Sig alg1 t1  a

embedSigTag :: View alg1 (t ': t1) alg2 (t ': t2) => Sig alg1 (t ': t1) a -> Sig alg2 (t ': t2) a
embedSigTag = embedSig

unsafeExtractSigTag ::
    ( View alg1 '[s] alg2 (s:t)
    ) => Sig alg2 (s ': t) (Free (Sig alg2) t a) -> Sig alg1 '[s] (Free (Sig alg2) t a)
unsafeExtractSigTag = unsafeExtractSig

unsafeExtractSigTag0 ::
    ( View alg1 '[] alg2 t
    ) => Sig alg2 t (Free (Sig alg2) t a) -> Sig alg1 '[] (Free (Sig alg2) t a)
unsafeExtractSigTag0 = unsafeExtractSig

instance FAlgebra alg => View alg t alg t where
    embedSig = id
    unsafeExtractSig = id

--------------------------------------------------------------------------------

-- | An alternative method for constructing kinds of [Tag] that obeys the equality constraints
type family ConsTag (t::Tag) (ts::[Tag]) :: [Tag]

-- | 'mkFree' is a smart constructor that is implemented by either 'Free1' or 'Free0' depending on how 'ConsTag' is implemented
class MkFree s (t::[Tag]) a where
    mkFree :: proxy s -> f (ConsTag s t) (Free f t a) -> Free f (ConsTag s t) a

-- | The constrained free monad
data Free (f::[Tag]->Type->Type) (t::[Tag]) (a::Type) where
    Free1 :: FreeConstraints t a => f (s ': t) (Free f t a)  -> Free f (s ': t) a
    Free0 :: FreeConstraints t a => f       t  (Free f t a)  -> Free f       t  a
    Pure  :: AppTags t a -> Free f t a

-- | The constraints we are placing on the free monad
type family FreeConstraints (t::[Tag]) (a::Type) :: Constraint

instance
    ( Show      (AppTags t a)
    , Show      (f t (Free f t a))
    , ShowUntag (f t (Free f t a))
    ) => Show (Free f t a)
        where
    show (Free1 f) = "("++show f++")"
    show (Free0 f) = "("++show f++")"
    show (Pure  a) = show a

type family ShowUntag (f::Type) :: Constraint where
    ShowUntag (f (s ':  t) (Free f (s ':  t) a))  = Show (f (s ':  t) (Free f          t  a))
    ShowUntag a = ()

--------------------------------------------------------------------------------

newtype Var = Var String
    deriving (Eq)

instance Show Var where
    show (Var v) = v

var1 :: AppTags t Var~Var => AST alg t Var
var1 = Pure $ Var "var1"

var2 :: AppTags t Var~Var => AST alg t Var
var2 = Pure $ Var "var2"

var3 :: AppTags t Var~Var => AST alg t Var
var3 = Pure $ Var "var3"

--------------------------------------------------------------------------------

runSig0Snoc :: forall proxy alg a t u.
    ( FAlgebra alg
    , alg (AppTag u a)
    ) => Proxy u
      -> Proxy a
      -> Sig alg t (AppTags (t `Snoc` u) a)
      -> AppTags (t `Snoc` u) a
runSig0Snoc ps pa u
    = coerce_AppTags_Snoc pt ps pa $ runSig0 (Proxy::Proxy (AppTag u a)) $ coerce_AppTags_Snoc_f pt ps pa u
    where
        pt = Proxy :: Proxy t

type family Init (xs::[a]) where
    Init (x ': '[]) = '[]
    Init (x ': xs ) = x ': Init xs

runSig1Snoc :: forall proxy alg a s ttt t u.
    ( FAlgebra alg
    , alg (AppTag u a)
    ) => Proxy (u::Tag)
      -> Proxy (s::Tag)
      -> Proxy (t::[Tag])
      -> Proxy a
      -> Sig alg ttt (AppTags t a)
      -> AppTag s (AppTags t a)
runSig1Snoc pu ps pt pa s
    = unsafeCoerce $ runSig1
        (Proxy::Proxy (AppTag u a))
        (unsafeCoerce s :: Sig alg (s ': Init t) (AppTags (Init t) (AppTag u a)))

unsafeCoerceSigTag :: proxy t' -> Sig alg t a -> Sig alg t' a
unsafeCoerceSigTag _ = unsafeCoerce


--------------------------------------------------------------------------------

data HaskTag {-cxt-} a b where
    HaskTag ::
        ( forall (s::[Tag]). () --cxt s
            => Proxy s
--             -> Proxy cxt
            -> Proxy a
            -> Proxy b
            -> AppTags s a
            -> AppTags s b
        ) -> HaskTag a b

apHaskTag :: forall t a b . Proxy (t::[Tag]) -> HaskTag a b -> AppTags t a -> AppTags t b
apHaskTag pt (HaskTag f) = f pt (Proxy::Proxy a) (Proxy::Proxy b)

class FunctorTag (f::[Tag]->Type->Type) where
    fmapTag :: HaskTag a b -> f t a -> f t b

{-
embedAST :: forall alg1 alg2 cxt (s::[Tag]) t a.
    ( FAlgebra alg1
--     , FunctorTag (ValidView alg1 alg2 t) (Sig alg1)
    , FunctorTag (Sig alg1)
    , ValidView alg1 alg2 t s
    ) => HaskTag
--         (ValidView alg1 alg2 t)
        (Free (Sig alg1) t a)
        (Free (Sig alg2) t a)
embedAST = HaskTag go
    where
        go :: forall (s::[Tag]).
            ( FAlgebra alg1
            , FunctorTag (Sig alg1)
--             , FunctorTag (ValidView alg1 alg2 t) (Sig alg1)
            , ValidView alg1 alg2 t s
            ) => Proxy s
--               -> Proxy (ValidView alg1 alg2 t)
              -> Proxy (Free (Sig alg1) t a)
              -> Proxy (Free (Sig alg2) t a)
              -> AppTags s (Free (Sig alg1) t a)
              -> AppTags s (Free (Sig alg2) t a)
        go _ _ _ expr = case appFree @s @t @a @alg1 expr of
            (Pure a) -> appFree' @s @t @a @alg2 (Pure a)
            (Free f) -> appFree' @s @t @a @alg2
                $ Free
                $ embedSig
--                 $ _ embedAST f
                $ fmapTag  embedAST f
-- --             (Free1 f) -> appFree' @s @t @a @alg2
-- --                 $ Free1
-- --                 $ embedSig
-- --                 $ fmapTag @(ValidView alg1 alg2 t) embedAST f
-}

-- class NoCxt (a::k)
-- instance NoCxt a
--
-- haskEval :: forall cxt alg t a.
--     ( alg a
--     , FAlgebra alg
--     , FunctorTag (Sig alg)
--     ) => HaskTag (Free (Sig alg) t a) (AppTags t a)
-- haskEval = HaskTag go
--     where
--         go :: forall (s::[Tag]) .
--             ( alg a
--             , FAlgebra alg
--             , FunctorTag (Sig alg)
--             ) => Proxy s
-- --               -> Proxy cxt
--               -> Proxy (Free (Sig alg) t a)
--               -> Proxy (AppTags t a)
--               -> AppTags s (Free (Sig alg) t a)
--               -> AppTags s (AppTags t a)
--         go _ _ _ expr = case appFree @s @t @a @alg expr of
--             (Pure a) -> appApp
--                 (Proxy::Proxy s)
--                 (Proxy::Proxy t)
--                 (Proxy::Proxy a)
--                  a
--             (Free0 f) -> appApp
--                     (Proxy::Proxy s)
--                     (Proxy::Proxy t)
--                     (Proxy::Proxy a)
--                 $ runSig0 (Proxy::Proxy a)
--                 $ fmapTag haskEval f
--             (Free1 f) -> appApp
--                     (Proxy::Proxy s)
--                     (Proxy::Proxy t)
--                     (Proxy::Proxy a)
--                 $ runSig1 (Proxy::Proxy a)
--                 $ fmapTag haskEval f

-- appFree :: forall (s::[Tag]) t a alg. AppTags s (Free (Sig alg) t a) -> Free (Sig alg) (s++t) a
-- appFree = unsafeCoerce
--
-- appFree' :: forall (s::[Tag]) t a alg. Free (Sig alg) (s++t) a -> AppTags s (Free (Sig alg) t a)
-- appFree' = unsafeCoerce
--
-- appApp :: Proxy (s::[Tag]) -> Proxy t -> Proxy a -> AppTags (s++t) a -> AppTags s (AppTags t a)
-- appApp _ _ _ = unsafeCoerce

-- class
--     ( View alg1 (s++t) alg2 (s++t)
--     ) => ValidView
--         (alg1::Type->Constraint)
--         (alg2::Type->Constraint)
--         (t::[Tag])
--         (s::[Tag])
-- instance
--     ( View alg1 (s++t) alg2 (s++t)
--     ) => ValidView alg1 alg2 t s

