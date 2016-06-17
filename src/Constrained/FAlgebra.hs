{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilyDependencies #-}

{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

module Constrained.FAlgebra
    (
    -- *
      FAlgebra (..)
    , View (..)
    , Free (..)
    , AST
    , runAST
    , ParentClasses

    -- **
    , Tag
    , AppTag
    , AppTags
--     , TypeConstraints
    , TagConstraints
    , ConsTag
    , ConsTagCnst
    , MkFree (..)

    , Snoc

    -- **
    , FunctorTag (..)
    , apHaskTag
    , HaskTag

    -- * Template Haskell
    , mkTag
    , mkTag_
    , mkFAlgebra
    , superPredicates

    -- **
    , unsafeExtractSigTag0
    , unsafeExtractSigTag
    , unsafeCoerceSigTag
    , runSig1Snoc
    , runSig0Snoc
    , embedSigTag

    -- **
    , Proxy (..)
    , Typeable
    , Constraint

    -- *
    , Variety (..)
    , Law (..)
    , Var
    , var1
    , var2
    , var3
    )
    where

import Prelude
import Control.Monad
import Data.Foldable
import Data.List
import Data.Maybe
import Data.Typeable
import Data.Proxy

import Data.Kind
import GHC.Exts hiding (IsList(..))

import Test.Tasty
import Test.Tasty.Ingredients.Basic
import Test.Tasty.Options
import Test.Tasty.Runners
import qualified Test.Tasty.SmallCheck as SC
import qualified Test.Tasty.QuickCheck as QC
import Test.QuickCheck hiding (Testable)

import TemplateHaskellUtils
import Language.Haskell.TH hiding (Type)
import qualified Language.Haskell.TH as TH

import Debug.Trace

import Unsafe.Coerce

--------------------------------------------------------------------------------

type Tag = Type

type family AppTag (t::Tag) (a::Type)

type family AppTags (t::[Tag]) (a::Type) :: Type where
    AppTags '[]       a = a
    AppTags (x ': xs) a = AppTag x (AppTags xs a)

type family Snoc (xs :: [k]) (y::k) where
    Snoc '[]       y = '[y]
    Snoc (x ': xs) y = x ': (Snoc xs y)

-- type family Snoc (xs :: [k]) (y::k) = r | r -> xs y where
--     Snoc '[]       y = '[y]
--     Snoc '[x]      y = '[x,y]
--     Snoc '[x1,x2]  y = '[x1,x2,y]

type family (++) (xs1:: [x]) (xs2:: [x]) :: [x] where
    '[] ++ '[] = '[]
    '[] ++ xs2 = xs2
    xs1 ++ '[] = xs1
    (x ': xs1) ++ xs2 = x ': (xs1++xs2)

----------------------------------------

appCoerce
    :: Proxy t
    -> Proxy s
    -> Proxy a
    -> AppTags t (AppTag s a)
    -> AppTags (t `Snoc` s) a
appCoerce _ _ _ = unsafeCoerce

sigCoerce
    :: Proxy t
    -> Proxy s
    -> Proxy a
    -> Sig alg t (AppTags (t `Snoc` s) a)
    -> Sig alg t (AppTags  t (AppTag s a))
sigCoerce _ _ _ = unsafeCoerce

runSig0Snoc :: forall proxy alg a t u.
    ( FAlgebra alg
    , alg (AppTag u a)
    ) => Proxy u
--       -> Proxy u
      -> Proxy a
      -> Sig alg t (AppTags (t `Snoc` u) a)
      -> AppTags (t `Snoc` u) a
runSig0Snoc ps pa u
    = appCoerce pt ps pa $ runSig0 (Proxy::Proxy (AppTag u a)) $ sigCoerce pt ps pa u
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

----------------------------------------

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

----------------------------------------

type AST (alg::Type->Constraint) t a = Free (Sig alg) t a

type family ConsTag (t::Tag) (ts::[Tag]) :: [Tag]
type family ConsTagCnst (t::Tag) (ts::[Tag]) :: Constraint
type family TagConstraints (t::[Tag]) (a::Type) :: Constraint
class MkFree s (t::[Tag]) a where
    mkFree :: proxy s -> f (ConsTag s t) (Free f t a) -> Free f (ConsTag s t) a

data Free (f::[Tag]->Type->Type) (t::[Tag]) (a::Type) where
    Free1 :: TagConstraints t a => f (s ': t) (Free f t a)  -> Free f (s ': t) a
    Free0 :: TagConstraints t a => f       t  (Free f t a)  -> Free f       t  a
    Pure  :: AppTags t a -> Free f t a

-- instance
--     ( Show (AppTag s (AppTags t a))
--     , Show (f (s ': t) (Free f (s ': t) a))
--     , Show (f (s ': t) (Free f       t  a))
--     ) => Show (Free f (s ': t) a)
--         where
--     show (Free1 f) = "("++show f++")"
--     show (Free0 f) = "("++show f++")"
--     show (Pure  a) = show a

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

runAST :: forall alg t a.
    ( FAlgebra alg
    , alg a
    ) => Free (Sig alg) t a -> AppTags t a
runAST (Pure  a) = a
runAST (Free0 s) = runSig0 (Proxy::Proxy a) $ mapRun runAST s
runAST (Free1 s) = runSig1 (Proxy::Proxy a) $ mapRun runAST s

class NoCxt (a::k)
instance NoCxt a

haskEval :: forall cxt alg t a.
    ( alg a
    , FAlgebra alg
    , FunctorTag (Sig alg)
    ) => HaskTag (Free (Sig alg) t a) (AppTags t a)
haskEval = HaskTag go
    where
        go :: forall (s::[Tag]) .
            ( alg a
            , FAlgebra alg
            , FunctorTag (Sig alg)
            ) => Proxy s
--               -> Proxy cxt
              -> Proxy (Free (Sig alg) t a)
              -> Proxy (AppTags t a)
              -> AppTags s (Free (Sig alg) t a)
              -> AppTags s (AppTags t a)
        go _ _ _ expr = case appFree @s @t @a @alg expr of
            (Pure a) -> appApp
                (Proxy::Proxy s)
                (Proxy::Proxy t)
                (Proxy::Proxy a)
                 a
            (Free0 f) -> appApp
                    (Proxy::Proxy s)
                    (Proxy::Proxy t)
                    (Proxy::Proxy a)
                $ runSig0 (Proxy::Proxy a)
                $ fmapTag haskEval f
            (Free1 f) -> appApp
                    (Proxy::Proxy s)
                    (Proxy::Proxy t)
                    (Proxy::Proxy a)
                $ runSig1 (Proxy::Proxy a)
                $ fmapTag haskEval f

class
    ( View alg1 (s++t) alg2 (s++t)
    ) => ValidView
        (alg1::Type->Constraint)
        (alg2::Type->Constraint)
        (t::[Tag])
        (s::[Tag])
instance
    ( View alg1 (s++t) alg2 (s++t)
    ) => ValidView alg1 alg2 t s

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

appFree :: forall (s::[Tag]) t a alg. AppTags s (Free (Sig alg) t a) -> Free (Sig alg) (s++t) a
appFree = unsafeCoerce

appFree' :: forall (s::[Tag]) t a alg. Free (Sig alg) (s++t) a -> AppTags s (Free (Sig alg) t a)
appFree' = unsafeCoerce

appApp :: Proxy (s::[Tag]) -> Proxy t -> Proxy a -> AppTags (s++t) a -> AppTags s (AppTags t a)
appApp _ _ _ = unsafeCoerce

----------------------------------------

class Typeable alg => FAlgebra (alg::Type->Constraint) where
    data Sig alg (t::[Tag]) a

    runSig1 :: alg a => proxy a -> Sig alg (s ':  t) (AppTags t a) -> AppTags (s ':  t) a
    runSig0    :: alg a => proxy a -> Sig alg        t  (AppTags t a) -> AppTags        t  a

    mapRun :: (TagConstraints t' a)
         => (forall s. Free (Sig alg') s a -> AppTags s a)
         -> Sig alg t (Free (Sig alg') t' a)
         -> Sig alg t (AppTags t' a)

--     mapf :: (TypeConstraints t' a)
--          => (forall s. Free (Sig alg') s a -> Free (Sig alg') s a)
--          -> Sig alg t (Free (Sig alg') t' a)
--          -> Sig alg t (Free (Sig alg') t' a)

----------------------------------------

class (FAlgebra alg1, FAlgebra alg2) => View alg1 t1 alg2 t2 where
    embedSig          :: Sig alg1       t1  a -> Sig alg2       t2  a
    unsafeExtractSig  :: Sig alg2       t2  a -> Sig alg1       t1  a

--     embedAST         :: Free (Sig alg1) t1 a -> Free (Sig alg2) t2 a
--     unsafeExtractAST :: Free (Sig alg2) t2 a -> Free (Sig alg1) t1 a

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

data Law alg t = Law
    { lawName :: String
    , lhs :: AST alg t Var
    , rhs :: AST alg t Var
    }

deriving instance Show (AST alg t Var) => Show (Law alg t)

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

--------------------

-- type Op0 alg = AST alg Var
-- type Op1 alg = AST alg Var -> AST alg Var
-- type Op2 alg = AST alg Var -> AST alg Var -> AST alg Var
--
-- commutative :: Op2 alg -> Law alg
-- commutative f = Law
--     { lawName = "commutative"
--     , lhs = f var1 var2
--     , rhs = f var2 var1
--     }
--
-- associative :: Op2 alg -> Law alg
-- associative f = Law
--     { lawName = "associative"
--     , lhs = (var1 `f`  var2) `f` var3
--     , rhs =  var1 `f` (var2  `f` var3)
--     }
--
-- idempotent :: Op2 alg -> Law alg
-- idempotent f = Law
--     { lawName = "idempotent"
--     , lhs = f var1 var1
--     , rhs = var1
--     }
--
-- identity_left :: Op0 alg -> Op2 alg -> Law alg
-- identity_left f0 f2 = Law
--     { lawName = "identity_left"
--     , lhs = f2 f0 var1
--     , rhs = var1
--     }
--
-- identity_right :: Op0 alg -> Op2 alg -> Law alg
-- identity_right f0 f2 = Law
--     { lawName = "identity_right"
--     , lhs = f2 var1 f0
--     , rhs = var1
--     }

--------------------

-- type family AncestorClasses (t::Type->Constraint) :: [Type -> Constraint]

type ClassSig = (Type->Constraint,[Tag])

type family ParentClasses (alg::ClassSig) :: [ClassSig]

type AncestorClasses alg = Nub (AncestorClasses_ (ParentClasses alg))

type family AncestorClasses_ (xs::[ClassSig]) :: [ClassSig] where
    AncestorClasses_ (x ': xs) = x ': (AncestorClasses_ (ParentClasses x) ++ AncestorClasses_ xs)
    AncestorClasses_ '[] = '[]

-- type family (++) (xs1:: [x]) (xs2:: [x]) :: [x] where
--     '[] ++ '[] = '[]
--     '[] ++ xs2 = xs2
--     xs1 ++ '[] = xs1
--     (x ': xs1) ++ xs2 = x ': (xs1++xs2)

type family Nub xs where
    Nub '[] = '[]
    Nub (x ': xs) = x ': Nub (Remove x xs)

type family Remove x xs where
    Remove x '[]       = '[]
    Remove x (x ': ys) =      Remove x ys
    Remove x (y ': ys) = y ': Remove x ys

--------------------

-- class (FAlgebra alg , ListLaws alg (AncestorClasses '(alg,'[]))) => Variety alg where
class FAlgebra alg => Variety alg where
    laws :: [Law alg '[]]

-- class Variety alg => ListLaws alg (xs::[ClassSig]) where
--     listLaws :: Proxy xs -> [(TypeRep,[Law alg '[]])]
--
-- instance Variety alg => ListLaws alg '[] where
--     listLaws _ = []
--
-- instance
--     ( Variety alg
--     , Variety alg'
--     , View alg' t' alg '[]
--     , ListLaws alg xs
--     , Typeable t'
--     ) => ListLaws alg ( '(alg',t') ': xs)
--         where
--     listLaws _ =
--         [ (typeRep (Proxy::Proxy alg'), embedLaws (laws::[Law alg' t'])) ]
--         ++
--         listLaws (Proxy::Proxy xs)
--
-- allLaws :: forall alg t. ListLaws alg (AncestorClasses '(alg,'[])) => [(TypeRep,[Law alg '[]])]
-- allLaws = listLaws (Proxy::Proxy (AncestorClasses '(alg,'[])))

--------------------

-- embedLaw :: View alg1 t1 alg2 t2 => Law alg1 t1 -> Law alg2 t2
-- embedLaw law = law
--     { lhs = embedAST $ lhs law
--     , rhs = embedAST $ rhs law
--     }
--
-- embedLaws :: View alg1 t1 alg2 t2 => [Law alg1 t1] -> [Law alg2 t2]
-- embedLaws = map embedLaw

--------------------------------------------------------------------------------

-- printAllLaws :: forall alg.
--     ( Variety alg
--     , Show (AST alg Var)
--     ) => IO ()
-- printAllLaws = do
--     forM (allLaws @alg) $ \(t,laws) -> do
--         putStrLn $ show t
--         forM laws $ \law -> do
--             printLaw law
--
--     putStrLn $ show $ typeRep (Proxy::Proxy alg)
--     printLaws (Proxy::Proxy alg)
--     putStrLn ""

printLaws :: forall alg.
    ( Variety alg
    , Show (AST alg '[] Var)
    ) => Proxy alg -> IO ()
printLaws palg = do
    forM_ (laws::[Law alg '[]]) printLaw

printLaw :: Show (AST alg t Var) => Law alg t -> IO ()
printLaw law = do
    putStrLn $ "  "++lawName law++":"
    putStrLn $ "    lhs: "++show (lhs law)
    putStrLn $ "    rhs: "++show (rhs law)

----------------------------------------

type Testable a = (Eq a, Arbitrary a, Typeable a)

-- subVars :: (Functor (Sig alg t), FAlgebra alg) => AST alg t Var -> [(Var,a)] -> AST alg t a
-- subVars expr varmap = fmap go expr
--     where
--         go var = case lookup var varmap of
--             Just a -> a
--
-- law2quickcheck :: forall (a::Type) alg t.
--     ( FAlgebra alg
--     , alg a
--     , Testable a
--     ) => Proxy a -> Law alg t -> TestTree
-- law2quickcheck p law = QC.testProperty (lawName law) $ do
--     as <- infiniteListOf (arbitrary::Gen a)
--     let varmap = zip (toList (lhs law) ++ toList (rhs law)) as
--     return $ (runAST $ subVars (lhs law) varmap)
--           == (runAST $ subVars (rhs law) varmap)

--------------------------------------------------------------------------------

-- |
--
-- FIXME:
-- Currently, only "Scalar" is idempotent and nothing else is.
isIdempotent :: Name -> Q Bool
isIdempotent n = return $ if nameBase n=="Scalar" || nameBase n =="Logic"
    then True
    else False

-- | Constructs the needed declarations for a type family assuming no constraints on the type family
mkTag :: Name -> Q [Dec]
mkTag = mkTag_ []

-- | Constructs the declarations for a type family that is constrainted by some context.
-- Currently, the only supported constraints are idempocency constraints.
mkTag_ :: Cxt -> Name -> Q [Dec]
mkTag_ cxt atName = do

    -- validate input
    qinfo <- reify atName
    case qinfo of
        FamilyI (OpenTypeFamilyD (TypeFamilyHead _ [_] _ _)) _ -> return ()
        _ -> error $ "mkAt called on "
            ++show atName
            ++", which is not an open type family of kind `Type -> Type`"

    -- common names
    let tagName = mkName $ "T"++nameBase atName

    --------------------
    -- all tags need these declarations

    -- construct the data Tag
    let decT = DataD
            []
            tagName
            []
            Nothing
            [NormalC tagName []]
            []

    -- construct the AppTags instance
    let instApp = TySynInstD
            ( mkName "AppTag" )
            ( TySynEqn
                [ ConT tagName, VarT $ mkName "a" ]
                ( AppT
                    ( ConT atName )
                    ( VarT $ mkName "a" )
                )
            )

    -- generate an overlappable MkFree instance that always behave like Free1
    let instMkFreeOverlap = InstanceD
            ( Just Overlappable )
            [ AppT
                ( AppT
                    ( ConT $ mkName "TagConstraints" )
                    ( VarT $ mkName "t" )
                )
                ( VarT $ mkName "a" )
            , AppT
                ( AppT
                    EqualityT
                    ( AppT
                        ( AppT
                            ( ConT $ mkName "ConsTag" )
                            ( ConT $ tagName )
                        )
                        ( VarT $ mkName "t" )
                    )
                )
                ( AppT
                    ( AppT
                        PromotedConsT
                        ( ConT $ tagName )
                    )
                    ( VarT $ mkName "t" )
                )
            ]
            ( AppT
                ( AppT
                    ( AppT
                        ( ConT $ mkName "MkFree" )
                        ( ConT $ tagName )
                    )
                    ( VarT $ mkName "t" )
                )
                ( VarT $ mkName "a" )
            )
            [ FunD
                ( mkName "mkFree" )
                [ Clause
                    [ VarP $ mkName "p" ]
                    ( NormalB $ ConE $ mkName "Free1" )
                    []
                ]
            ]

    --------------------
    -- these declarations depend on the tag's cxt
    let cxt' = flip filter cxt $ \t -> case t of
            (AppT (AppT EqualityT _) _) -> True
            (AppT (AppT (ConT n) _) _) -> show n == "Data.Type.Equality.~"
            _ -> False

    cnsts <- return $ case cxt' of

        -- there's no constraints
        [] ->
            -- ConsTag is the same as PromotedConsT
            [ TySynInstD
                ( mkName "ConsTag" )
                ( TySynEqn
                    [ ConT tagName , VarT $ mkName "ts" ]
                    ( AppT
                        ( AppT
                            PromotedConsT
                            ( ConT tagName )
                        )
                        ( VarT $ mkName "ts" )
                    )
                )
            ]

        -- there's exactly one idempotency constraint
        -- FIXME:
        -- the check that the constraint is an idempotency is not restrictive enough
        cnst@[(AppT (AppT _ t1) t2)] -> if maxDepth/=minDepth+1
            then error $ "mkTag_ constraint too complex: "++show cnst
            else
                -- ConsTag needs to call out to the ConsTag_algName closed family
                [ TySynInstD
                    ( mkName "ConsTag" )
                    ( TySynEqn
                        [ ConT tagName , VarT $ mkName "ts" ]
                        ( AppT
                            ( ConT $ mkName $ "ConsTag_"++nameBase tagName )
                            ( VarT $ mkName "ts" )
                        )
                    )

                -- create the ConsTag_algName closed family
                , ClosedTypeFamilyD
                    ( TypeFamilyHead
                        ( mkName $ "ConsTag_"++nameBase tagName )
                        [ PlainTV $ mkName "ts" ]
                        NoSig
                        Nothing
                    )
                    [ let t = foldl'
                            ( \b _ -> AppT
                                ( AppT
                                    PromotedConsT
                                    ( ConT tagName )
                                )
                                b
                            )
                            ( VarT $ mkName "ts" )
                            ( replicate minDepth () )
                      in TySynEqn [t] (t)
                    , TySynEqn
                        [ VarT $ mkName "ts" ]
                        ( AppT
                            ( AppT
                                PromotedConsT
                                ( ConT tagName )
                            )
                            ( VarT $ mkName "ts" )
                        )
                    ]
                ]
                ++
                -- create MkFree instances
                [ let tagsType =
                        ( foldl'
                            ( \b _ -> AppT
                                ( AppT
                                    PromotedConsT
                                    ( ConT tagName )
                                )
                                b
                            )
                            ( if i==minDepth
                                then VarT $ mkName "t"
                                else PromotedNilT
                            )
                            ( replicate i () )
                        )
                  in InstanceD
                    Nothing
                    [ AppT
                        ( AppT
                            ( ConT $ mkName "TagConstraints" )
                            tagsType
                        )
                        ( VarT $ mkName "a" )
                    ]
                    ( AppT
                        ( AppT
                            ( AppT
                                ( ConT $ mkName "MkFree" )
                                ( ConT $ tagName )
                            )
                            tagsType
                        )
                        ( VarT $ mkName "a" )
                    )
                    [ FunD
                        ( mkName "mkFree" )
                        [ Clause
                            [ VarP $ mkName "p" ]
                            ( NormalB $ ConE $ if i==minDepth
                                then mkName "Free0"
                                else mkName "Free1"
                            )
                            []
                        ]
                    ]
                | i <- [0..minDepth]
                ]


            where
                maxDepth = max (depthSameAppT t1) (depthSameAppT t2)
                minDepth = min (depthSameAppT t1) (depthSameAppT t2)

    return $ cnsts ++ [instMkFreeOverlap, decT, instApp]

-- | Generates the FAlgebra instance for the specified name and all of its dependencies recursively
mkFAlgebra :: Name -> Q [Dec]
mkFAlgebra algName = do

    -- validate input and extract the class functions
    qinfo <- reify algName
    (cxt,rawdecs) <- case qinfo of
        ClassI (ClassD cxt _ [_] _ decs) _ -> return (cxt,decs)
        _ -> error $ "mkFAlgebra called on "
            ++show algName
            ++", which is not a class of kind `Type -> Constraint`"

    -- common variables we'll need later
    allcxt <- superPredicates $ AppT (ConT algName) (VarT $ mkName "t")

    -- For all the superclasses without FAlgebras, generate them
    prereqs <- fmap (nub . concat) $ sequence
        [ do
            qinfo <- reify ''FAlgebra
            case qinfo of
                (ClassI _ insts) -> do
                    if (ConT predClass) `elem` map (\(InstanceD _ _ (AppT _ t) _) -> t) insts
                        then return []
                        else mkFAlgebraNoRec predClass
        | PredInfo (AppT (ConT predClass) _) _ _ <- allcxt
        ]

    return prereqs


-- | Generates the FAlgebra instance for the specified name without recusively generating dependencies
mkFAlgebraNoRec :: Name -> Q [Dec]
mkFAlgebraNoRec algName = do

    -- validate input and extract the class functions
    qinfo <- reify algName
    (cxt,rawdecs) <- case qinfo of
        ClassI (ClassD cxt _ [_] _ decs) _ -> return (cxt,decs)
        _ -> error $ "mkFAlgebraNoRec called on "
            ++show algName
            ++", which is not a class of kind `Type -> Constraint`"

    -- remove functions from decsraw that we can't handle
    let go x = case x of
            SigD _ sigType -> if isConcrete $ getReturnType sigType
                then False
                else True
            _ -> True
    let decs = filter go rawdecs

    -- common variables we'll need later
    let varName = mkName "a"
        tagName = mkName "t"
        thisPred = AppT (ConT algName) (VarT tagName)
    allcxt <- superPredicates thisPred

    -- construct associated types
    -- FIXME:
    -- Should this construct non-associated types that happen to be used as well?
    -- If so, should we prevent duplicate instances from being created?
    ats <- fmap concat $ sequence
        [ mkTag_ cxt atName
        | OpenTypeFamilyD (TypeFamilyHead atName _ _ _) <- decs
        ]

    -- create a constructor for each member function
    let consFunc =
            [ GadtC
                [ mkName $ "Sig_" ++ renameClassMethod sigName ]
                ( map
                    ( Bang NoSourceUnpackedness NoSourceStrictness,)
                    ( getArgs $ subForall varName sigType)
                )
                ( AppT
                    ( AppT
                        ( AppT
                            ( ConT $ mkName "Sig" )
                            ( ConT $ algName )
                        )
                        ( pred2tag PromotedNilT $ getReturnType $ subForall varName sigType )
                    )
                    ( VarT varName )
                )
                | SigD sigName sigType <- decs
            ]

    -- create a constructor for each predicate class to hold their signatures
    let consPred =
            [ GadtC
                [ mkName $ "Sig_"++nameBase algName
                            ++"_"++nameBase predClass
                            ++"_"++predType2str predType
                ]
                [ ( Bang SourceUnpack SourceStrict
                  , AppT
                    ( AppT
                        ( AppT
                            ( ConT $ mkName "Sig" )
                            ( ConT predClass )
                        )
                        ( VarT tagName )
                    )
                    ( VarT varName )
                  )
                ]
                ( AppT
                    ( AppT
                        ( AppT
                            ( ConT $ mkName "Sig" )
                            ( ConT $ algName )
                        )
                        ( case predType of
                            (VarT _) -> VarT tagName
                            _        -> AppT
                                ( AppT
                                    ( ConT $ mkName "Snoc" )
                                    ( VarT tagName )
                                )
                                ( pred2tagSingleton predType )
                        )
                    )
                    ( VarT varName )
                )
                | AppT (ConT predClass) predType <- cxt
            ]

    -- construct the FAlgebra instance
    let instFAlgebra = InstanceD
            Nothing
            []
            ( AppT
                ( ConT $ mkName "FAlgebra" )
                ( ConT $ algName)
            )
            [ DataInstD
                []
                ( mkName "Sig" )
                [ ConT algName, VarT tagName, VarT varName ]
                Nothing
                ( consFunc++consPred )
                []

            , FunD
                ( mkName "mapRun" )
                (
                    -- for each function constructor
                    [ Clause
                        [ VarP $ mkName "f"
                        , ConP
                            ( mkName $ "Sig_" ++ renameClassMethod sigName )
                            ( map VarP $ genericArgs sigType )
                        ]
                        ( NormalB $ foldl
                            AppE
                            ( ConE $ mkName $ "Sig_"++renameClassMethod sigName )
                            [ if not $ isConcrete argType
                                then AppE
                                    ( VarE $ mkName "f" )
                                    ( VarE $ argName )
                                else VarE argName
                            | (argName,argType) <- zip
                                (genericArgs sigType)
                                (getArgs sigType)
                            ]
                        )
                        []
                        | SigD sigName sigType <- decs
                    ]
                    ++
                    -- for each predicate constructor
                    [ Clause
                        [ VarP $ mkName "f"
                        , ConP ( mkName $ "Sig_"++nameBase algName
                                           ++"_"++nameBase predClass
                                           ++"_"++predType2str predType
                               )
                               [ VarP $ mkName "s" ]
                        ]
                        ( NormalB
                            ( AppE
                                ( ConE $ mkName $ "Sig_"++nameBase algName
                                                   ++"_"++nameBase predClass
                                                   ++"_"++predType2str predType
                                )
                                ( AppE
                                    ( AppE
                                        ( VarE $ mkName "mapRun" )
                                        ( VarE $ mkName "f" )
                                    )
                                    ( VarE $ mkName "s" )
                                )
                            )
                        )
                        []
                    | AppT (ConT predClass) predType <- cxt
                    ]
                    ++
                    -- catch all error message
                    [ Clause
                        [ VarP $ mkName "f", VarP $ mkName "s" ]
                        ( NormalB $ AppE
                            ( VarE $ mkName "error" )
                            ( LitE $ StringL $ "mapRun ("++nameBase algName++"): this should never happen" )
                        )
                        []
                    ]
                )
            , FunD
                ( mkName "runSig1" )
                (
                    -- evaluate functions
                    ( catMaybes [ case getReturnType sigType of
                        (VarT _) -> Nothing
                        _ -> Just $ Clause
                            [ SigP
                                ( VarP $ mkName "p" )
                                ( AppT
                                    ( VarT $ mkName "proxy" )
                                    ( VarT $ mkName "r" )
                                )
                            , ConP
                                ( mkName $ "Sig_" ++ renameClassMethod sigName )
                                ( map VarP ( genericArgs sigType ) )
                            ]
                            ( NormalB $ foldl AppE (VarE sigName) $ map VarE $ genericArgs sigType )
                            []
                    | SigD sigName sigType <- decs
                    ] )
                    ++
                    -- evaluate nested constructors
                    [ Clause
                        [ SigP
                            ( VarP $ mkName "p" )
                            ( AppT
                                ( VarT $ mkName "proxy" )
                                ( VarT varName )
                            )
                        , SigP
                            ( ConP
                                ( mkName $ "Sig_"++nameBase algName
                                            ++"_"++nameBase predClass
                                            ++"_"++predType2str predType
                                )
                                [ VarP $ mkName $ "s" ]
                            )
                            ( AppT
                                ( AppT
                                    ( AppT
                                        ( ConT $ mkName "Sig" )
                                        ( ConT $ algName )
                                    )
                                    ( AppT
                                        ( AppT
                                            PromotedConsT
                                            ( VarT $ mkName "s" )
                                        )
                                        ( VarT $ mkName "t" )
                                    )
                                )
                                ( AppT
                                    ( AppT
                                        ( ConT $ mkName "AppTags" )
                                        ( VarT $ mkName "t" )
                                    )
                                    ( VarT $ mkName "a" )
                                )
                            )
                        ]
                        ( NormalB $ case predType of
                            (VarT _) -> AppE
                                ( AppE
                                    ( VarE $ mkName "runSig1" )
                                    ( VarE $ mkName "p" )
                                )
                                ( VarE $ mkName "s" )
                            _ -> AppE
                                ( AppE
                                    ( AppE
                                        ( AppE
                                            ( AppE
                                                ( VarE $ mkName "runSig1Snoc" )
                                                ( mkProxyE $ pred2tagSingleton predType )
                                            )
                                            ( mkProxyE $ VarT $ mkName "s" )
                                        )
                                        ( mkProxyE $ VarT $ mkName "t" )
                                    )
                                    ( mkProxyE $ VarT $ mkName "a" )
                                )
                                ( VarE $ mkName "s" )
                        )
                        []
                        | AppT (ConT predClass) predType <- cxt
                    ]
                    ++
                    -- catch all error message
                    [ Clause
                        [ VarP $ mkName "p", VarP $ mkName "s" ]
                        ( NormalB $ AppE
                            ( VarE $ mkName "error" )
                            ( LitE $ StringL $ "runSig1 ("++nameBase algName++"): this should never happen" )
                        )
                        []
                    ]
                )
            , FunD
                ( mkName "runSig0" )
                (
                    -- evaluate functions
                    ( catMaybes [ case getReturnType sigType of
                        (VarT _) -> Just $ Clause
                            [ SigP
                                ( VarP $ mkName "p" )
                                ( AppT
                                    ( VarT $ mkName "proxy" )
                                    ( VarT $ mkName "r" )
                                )
                            , ConP
                                ( mkName $ "Sig_" ++ renameClassMethod sigName )
                                ( map VarP ( genericArgs sigType ) )
                            ]
                            ( NormalB $ foldl AppE (VarE sigName) $ map VarE $ genericArgs sigType )
                            []
                        _ -> Nothing
                    | SigD sigName sigType <- decs
                    ] )
                    ++
                    -- evaluate nested constructors
                    [ Clause
                        [ SigP
                            ( VarP $ mkName "p" )
                            ( AppT
                                ( VarT $ mkName "proxy" )
                                ( VarT varName )
                            )
                        , ConP
                            ( mkName $ "Sig_"++nameBase algName
                                        ++"_"++nameBase predClass
                                        ++"_"++predType2str predType
                            )
                            [ VarP $ mkName $ "s" ]
                        ]
                        ( NormalB $  case predType of
                            (VarT _) -> AppE
                                ( AppE
                                    ( VarE $ mkName "runSig0" )
                                    ( VarE $ mkName "p" )
                                )
                                ( VarE $ mkName "s" )

                            _ -> AppE
                                ( AppE
                                    ( AppE
                                        ( VarE $ mkName "runSig0Snoc" )
                                        ( SigE
                                            ( ConE $ mkName "Proxy" )
                                            ( AppT
                                                ( ConT $ mkName "Proxy" )
                                                ( pred2tagSingleton predType )
                                            )
                                        )
                                    )
                                    ( SigE
                                        ( ConE $ mkName "Proxy" )
                                        ( AppT
                                            ( ConT $ mkName "Proxy" )
                                            ( VarT $ mkName "a" )
                                        )
                                    )
                                )
                                ( VarE $ mkName "s" )
                        )
                        []
                        | AppT (ConT predClass) predType <- cxt
                    ]
                    ++
                    -- catch all error message
                    [ Clause
                        [ VarP $ mkName "p", VarP $ mkName "s" ]
                        ( NormalB $ AppE
                            ( VarE $ mkName "error" )
                            ( LitE $ StringL $ "runSig0 ("++nameBase algName++"): this should never happen" )
                        )
                        []
                    ]
                )
            ]

    -- construct pattern synonyms
    --
    -- FIXME:
    -- The pattern synonyns for the tagged and untagged versions are currently split into two separate cases.
    -- There's a lot of overlap in them though, and so the code would probably be nicer to merge the two cases.
    let patSyns = concat $
            [ if isVarT $ getReturnType sigType
                then
                    [ PatSynSigD
                        ( mkName $ "AST_" ++ renameClassMethod sigName )
                        ( ForallT
                            [ PlainTV $ mkName "alg"
                            , PlainTV tagName
                            , PlainTV varName
                            ]
                            [ AppT
                                ( AppT
                                    ( AppT
                                        ( AppT
                                            ( ConT $ mkName "View" )
                                            ( ConT $ algName )
                                        )
                                        PromotedNilT
                                    )
                                    ( VarT $ mkName "alg" )
                                )
                                ( VarT tagName )
                            , AppT
                                ( AppT
                                    ( ConT $ mkName "TagConstraints" )
                                    ( VarT tagName )
                                )
                                ( VarT varName )
                            ]
                            ( foldr
                                (\a b -> AppT
                                    ( AppT
                                        ArrowT
                                        ( if isConcrete a
                                            then a
                                            else AppT
                                                ( AppT
                                                    ( AppT
                                                        ( ConT $ mkName "Free" )
                                                        ( AppT
                                                            ( ConT $ mkName "Sig" )
                                                            ( VarT $ mkName "alg" )
                                                        )
                                                    )
                                                    ( if isVarT a
                                                        then VarT tagName
                                                        else pred2tag (VarT tagName) a
                                                    )
                                                )
                                                ( VarT varName )
                                        )
                                    )
                                    b
                                )
                                ( AppT
                                    ( AppT
                                        ( AppT
                                            ( ConT $ mkName "Free" )
                                            ( AppT
                                                ( ConT $ mkName "Sig" )
                                                ( VarT $ mkName "alg" )
                                            )
                                        )
                                        ( VarT tagName )
                                    )
                                    ( VarT varName )
                                )
                                ( getArgs sigType )
                            )
                        )
                    , PatSynD
                        ( mkName $ "AST_" ++ renameClassMethod sigName )
                        ( PrefixPatSyn $ genericArgs sigType )
                        ( ExplBidir
                            [ Clause
                                ( map VarP $ genericArgs sigType )
                                ( NormalB $ AppE
                                    ( ConE $ mkName "Free0" )
                                    ( AppE
                                        ( VarE $ mkName "embedSig" )
                                        ( foldl
                                            AppE
                                            ( ConE $ mkName $ "Sig_" ++ renameClassMethod sigName )
                                            ( map VarE $ genericArgs sigType )
                                        )
                                    )
                                )
                                []
                            ]
                        )
                        ( ConP
                            ( mkName "Free0" )
                            [ ViewP
                                ( VarE $ mkName "unsafeExtractSigTag0" )
                                ( ConP
                                    ( mkName $ "Sig_" ++ renameClassMethod sigName )
                                    ( map VarP $ genericArgs sigType )
                                )
                            ]
                        )
                    ]
                else
                    [ PatSynSigD
                        ( mkName $ "AST_" ++ renameClassMethod sigName )
                        ( ForallT
                            [ PlainTV $ mkName "alg"
                            , PlainTV tagName
                            , PlainTV varName
                            ]
                            [ AppT
                                ( AppT
                                    ( AppT
                                        ( AppT
                                            ( ConT $ mkName "View" )
                                            ( ConT $ algName )
                                        )
                                        ( pred2tag PromotedNilT $ getReturnType sigType )
                                    )
                                    ( VarT $ mkName "alg" )
                                )
                                ( pred2tag (VarT tagName) $ getReturnType sigType )
                            , AppT
                                ( AppT
                                    ( ConT $ mkName "TagConstraints" )
                                    ( VarT tagName )
                                )
                                ( VarT varName )
                            ]
                            ( foldr
                                (\a b -> AppT
                                    ( AppT
                                        ArrowT
                                        ( AppT
                                            ( AppT
                                                ( AppT
                                                    ( ConT $ mkName "Free" )
                                                    ( AppT
                                                        ( ConT $ mkName "Sig" )
                                                        ( VarT $ mkName "alg" )
                                                    )
                                                )
                                                ( if isVarT a
                                                    then VarT tagName
                                                    else pred2tag (VarT tagName) a
                                                )
                                            )
                                            ( VarT varName )
                                        )
                                    )
                                    b
                                )
                                ( AppT
                                    ( AppT
                                        ( AppT
                                            ( ConT $ mkName "Free" )
                                            ( AppT
                                                ( ConT $ mkName "Sig" )
                                                ( VarT $ mkName "alg" )
                                            )
                                        )
                                        ( if isVarT $ getReturnType sigType
                                            then VarT tagName
                                            else pred2tag (VarT tagName) $ getReturnType sigType
                                        )
                                    )
                                    ( VarT varName )
                                )
                                ( getArgs sigType )
                            )
                        )

                    , PatSynD
                        ( mkName $ "AST_" ++ renameClassMethod sigName )
                        ( PrefixPatSyn $ genericArgs sigType )
                        ( ExplBidir
                            [ Clause
                                ( map VarP $ genericArgs sigType )
                                ( NormalB $ AppE
                                    ( ConE $ mkName "Free1" )
                                    ( AppE
                                        ( VarE $ mkName "embedSigTag" )
                                        ( foldl
                                            AppE
                                            ( ConE $ mkName $ "Sig_" ++ renameClassMethod sigName )
                                            ( map VarE $ genericArgs sigType )
                                        )
                                    )
                                )
                                []
                            ]
                        )
                        ( ConP
                            ( mkName "Free1" )
                            [ ViewP
                                ( VarE $ mkName "unsafeExtractSigTag" )
                                ( ConP
                                    ( mkName $ "Sig_" ++ renameClassMethod sigName )
                                    ( map VarP $ genericArgs sigType )
                                )
                            ]
                        )
                    ]
            | SigD sigName sigType <- decs
            ]

    -- construct the overlapping Show instance
    let instShowOverlap = InstanceD
            ( Just Overlapping )
            []
            ( AppT
                ( ConT $ mkName "Show" )
                ( AppT
                    ( AppT
                        ( AppT
                            ( ConT $ mkName "Sig" )
                            ( ConT algName )
                        )
                        ( foldr
                            (\a b -> AppT
                                ( AppT
                                    PromotedConsT
                                    ( VarT $ mkName $ "t"++show a )
                                )
                                b
                            )
                            PromotedNilT
                            [1..4]
                        )
                    )
                    ( VarT $ varName )
                )
            )
            [ FunD
                ( mkName "show" )
                [ Clause
                    [ VarP $ mkName "s" ]
                    ( NormalB $ LitE $ StringL "<<overflow>>" )
                    []
                ]
            ]

    -- construct the `Show a => Show (Sig98 alg a)` instance
    let instShow = InstanceD
            ( Just Overlappable )
            (
                (nub $ concat $ concat $ concat $
                [   [   [ case t of
                            ( ConT _ ) -> []
                            _          -> [ AppT
                                ( ConT $ mkName "Show" )
                                ( subAllVars (VarT varName) t )
                                ]
                        | t <- getReturnType sigType:getArgs sigType
                        ]
                    | SigD sigName sigType <- decs
                    ]
                | PredInfo
                    (AppT (ConT predClass) predType)
                    (ClassI (ClassD _ _ _ _ decs) _)
                    _
                    <- allcxt
                ])

--                 nub $
--                 ( concat $ concat $
--                     [   [ case t of
--                             ( ConT _ ) -> []
--                             _          -> [ AppT
--                                 ( ConT $ mkName "Show" )
--                                 ( subAllVars (VarT varName) t )
--                                 ]
--                         | t <- getReturnType sigType:getArgs sigType
--                         ]
--                     | SigD sigName sigType <- decs
--                     ]
--                 )
--                 ++
--                 [ AppT
--                     ( ConT $ mkName "Show" )
--                     ( AppT
--                         ( AppT
--                             ( AppT
--                                 ( ConT $ mkName "Sig" )
--                                 ( ConT predClass )
--                             )
--                             ( case predType of
--                                 (VarT _) -> VarT tagName
--                                 _        -> AppT
--                                     ( AppT
--                                         ( ConT $ mkName "Snoc" )
--                                         ( VarT tagName )
--                                     )
--                                     ( pred2tagSingleton predType )
--                             )
-- --                             ( VarT $ mkName "t" )
--                         )
--                         ( VarT $ mkName "a" )
--                     )
--                 | AppT (ConT predClass) predType <- cxt
--                 ]
            )
            ( AppT
                ( ConT $ mkName "Show" )
                ( AppT
                    ( AppT
                        ( AppT
                            ( ConT $ mkName "Sig" )
                            ( ConT algName )
                        )
                        ( VarT $ tagName )
                    )
                    ( VarT $ varName )
                )
            )
            [ FunD
                ( mkName "show" )
                (
                    -- show all the class's predicates
                    [ Clause
                        [ ConP
                            ( mkName $ "Sig_"++nameBase algName
                                        ++"_"++nameBase predClass
                                        ++"_"++predType2str predType
                            )
                            [ VarP $ mkName "s" ]
                        ]
                        ( NormalB $ AppE
                            ( VarE $ mkName "show" )
                            ( VarE $ mkName "s" )
                        )
                        []
                        | AppT (ConT predClass) predType <- cxt
                    ]
                    ++
                    -- show all the class's functions
                    [ Clause
                        [ ConP
                            ( mkName $ "Sig_" ++ renameClassMethod sigName )
                            ( map VarP $ genericArgs sigType )
                        ]
                        ( if isOperator (nameBase sigName)

                            -- if we're an operator, then there's exactly two arguments named a0, a1;
                            -- display the operator infix
                            then NormalB $ AppE
                                ( AppE
                                    ( VarE $ mkName "++" )
                                    ( AppE
                                        ( AppE
                                            ( VarE $ mkName "++" )
                                            ( AppE
                                                ( VarE $ mkName "show" )
                                                ( VarE $ mkName "a0" )
                                            )
                                        )
                                        ( LitE $ StringL $ nameBase sigName )
                                    )
                                )
                                ( AppE
                                    ( VarE $ mkName "show" )
                                    ( VarE $ mkName "a1" )
                                )

                            -- not an operator means we display the function prefix,
                            -- there may be anynumber 0 or more arguments that we have to fold over
                            else NormalB $ foldl
                                ( \b a -> AppE
                                    ( AppE
                                        ( VarE $ mkName "++" )
                                        ( AppE
                                            ( AppE
                                                ( VarE $ mkName "++" )
                                                b
                                            )
                                            ( LitE $ StringL " " )
                                        )
                                    )
                                    ( AppE
                                        ( VarE $ mkName "show" )
                                        a
                                    )
                                )
                                ( LitE $ StringL $ nameBase sigName )
                                ( map VarE $ genericArgs sigType )
                        )
                        []
                        | SigD sigName sigType <- decs
                    ]
                    ++
                    -- catch all error message
                    [ Clause
                        [ VarP $ mkName "s" ]
                        ( NormalB $ AppE
                            ( VarE $ mkName "error" )
                            ( LitE $ StringL $ "show ("++nameBase algName++"): this should never happen" )
                        )
                        []
                    ]
                )
            ]

    -- construct the `View alg '[] alg' t => alg (Free (Sig alg') t a)` instance
    let instFree = InstanceD
            Nothing
            ( nub $
                -- the `TagConstraints` instance
                (
                    [ AppT
                        ( AppT
                            ( ConT $ mkName "TagConstraints" )
                            ( type2tag predType )
                        )
                        ( VarT $ mkName "a" )
                    | PredInfo
                        (AppT (ConT predClass) predType)
                        _
                        _
                        <- allcxt
                    ]
                    ++
                    [ AppT
                        ( AppT
                            ( ConT $ mkName "TagConstraints" )
                            ( VarT $ mkName "t" )
                        )
                        ( VarT $ mkName "a" )
                    ]
                )
                ++
                -- the `View ...` constraints
                ( concat $
                    [   [ AppT
                            ( AppT
                                ( AppT
                                    ( AppT
                                        ( ConT $ mkName "View" )
                                        ( ConT predClass )
                                    )
                                    ( cons2consTag $ pred2tag PromotedNilT $ getReturnType sigType )
                                )
                                ( VarT $ mkName "alg'" )
                            )
                            ( cons2consTag $ pred2tag
                                ( pred2tag (VarT tagName) predType )
                                ( getReturnType sigType )
                            )
                        | SigD _ sigType <- decs
                        ]
                    | PredInfo
                        (AppT (ConT predClass) predType)
                        (ClassI (ClassD _ _ _ _ decs) _)
                        _
                        <- allcxt
                    ]
                )
                ++
                -- the ConsTagCnst constraints
                -- FIXME: ensure that `c` is set correctly
                ( concat $
                    [   [ AppT
                            ( AppT
                                EqualityT
                                ( type2tag $ subAllVars predType t1 )
                            )
                            ( type2tag $ subAllVars predType t2 )
                        | (AppT (AppT c t1) t2) <- cxt
                        ]
                    | PredInfo
                        (AppT (ConT predClass) predType)
                        (ClassI (ClassD cxt _ _ _ _) _)
                        _
                        <- allcxt
                    ]
                )
                ++
                -- MkFree instances
                -- FIXME: ensure that `c` is set correctly
                [ AppT
                    ( AppT
                        ( AppT
                            ( ConT $ mkName "MkFree" )
                            ( ConT $ mkName t )
                        )
                        ( foldl'
                            ( \b a -> AppT
                                ( AppT
                                    ( ConT $ mkName "ConsTag" )
                                    ( ConT $ mkName a )
                                )
                                b
                            )
                            ( VarT $ mkName "t" )
                            ts
                        )
                    )
                    ( VarT $ mkName "a" )
                | (t,ts) <- nub $ concat $ concat $
                    [   [ case t1 of
                            (AppT (ConT n) _) ->
                                [ ( "T"++nameBase n
                                  , (case pred2strList predType of
                                    [] -> []
                                    (s:_) -> if nameBase n==s
                                        then []
                                        else [s]
                                    )++(replicate i $ "T"++nameBase n )
                                  )
                                | i <- [0..min (depthSameAppT t1) (depthSameAppT t2)]
                                ]
                        | (AppT (AppT c t1) t2) <- cxt
                        ]
                    | PredInfo
                        (AppT (ConT predClass) predType)
                        (ClassI (ClassD cxt _ _ _ _) _)
                        _
                        <- allcxt
                    ]
                -- the section above genrates lists of the form
                -- [("TLogic",[])
                -- ,("TLogic",["TLogic"])
                -- ,("TLogic",["TLogic","TLogic"])
                -- ]
                ]
            )
            ( AppT
                ( ConT algName )
                ( AppT
                    ( AppT
                        ( AppT
                            ( ConT $ mkName "Free" )
                            ( AppT
                                ( ConT $ mkName "Sig" )
                                ( VarT $ mkName "alg'" )
                            )
                        )
                        ( VarT $ tagName )
                    )
                    ( VarT varName )
                )
            )
            (
                -- create associated types
                [ TySynInstD atName $ TySynEqn
                    [ AppT
                        ( AppT
                            ( AppT
                                ( ConT $ mkName "Free" )
                                ( AppT
                                    ( ConT $ mkName "Sig" )
                                    ( VarT $ mkName "alg'" )
                                )
                            )
                            ( VarT $ tagName )
                        )
                        ( VarT varName )
                    ]
                    ( AppT
                        ( AppT
                            ( AppT
                                ( ConT $ mkName "Free" )
                                ( AppT
                                    ( ConT $ mkName "Sig" )
                                    ( VarT $ mkName "alg'" )
                                )
                            )
                            ( AppT
                                ( AppT
--                                     PromotedConsT
                                    ( ConT $ mkName "ConsTag" )
                                    ( ConT $ mkName $ "T"++nameBase atName )
                                )
                                ( VarT $ tagName )
                            )
                        )
                        ( VarT varName )
                    )
                | OpenTypeFamilyD (TypeFamilyHead atName _ _ _) <- decs
                ]
                ++
                -- create associated functions
                [ FunD
                    sigName
                    [ Clause
                        ( map VarP $ genericArgs sigType )
                        ( NormalB $ case getReturnType sigType of
                            (VarT _) -> AppE
                                ( ConE $ mkName "Free0" )
                                ( AppE
                                    ( VarE $ mkName "embedSig" )
                                    ( foldl AppE (ConE $ mkName $ "Sig_"++renameClassMethod sigName)
                                        $ map VarE $ genericArgs sigType
                                    )
                                )
                            (AppT (ConT n) _) -> AppE
                                ( AppE
                                    ( VarE $ mkName "mkFree" )
                                    ( SigE
                                        ( ConE $ mkName "Proxy" )
                                        ( AppT
                                            ( ConT $ mkName "Proxy" )
                                            ( ConT $ mkName $ "T"++nameBase n )
                                        )
                                    )
                                )
                                ( AppE
                                    ( VarE $ mkName "embedSig" )
                                    ( foldl AppE (ConE $ mkName $ "Sig_"++renameClassMethod sigName)
                                        $ map VarE $ genericArgs sigType
                                    )
                                )
--                                 AppE
--                                     ( ConE $ mkName "Free1")
--                                     ( AppE
--                                         ( VarE $ mkName "embedSigTag" )
--                                         ( foldl AppE (ConE $ mkName $ "Sig_"++renameClassMethod sigName)
--                                             $ map VarE $ genericArgs sigType
--                                         )
--                                     )
                        )
                        []
                    ]
                | SigD sigName sigType <- decs
                ]
            )

    -- construct the `View alg alg'` instances
    let instViews = nub $ concat $
            [   [ InstanceD
                    Nothing
                    []
                    ( AppT
                        ( AppT
                            ( AppT
                                ( AppT
                                    ( ConT $ mkName "View" )
                                    ( ConT predClass )
                                )
                                ( pred2tag
                                    PromotedNilT
                                    ( getReturnType sigType )
                                )
                            )
                            ( ConT algName )
                        )
                        ( pred2tag
                            ( pred2tag PromotedNilT predType )
                            ( getReturnType sigType )
                        )
                    )
                    [ if parent==thisPred
                        -- parent predicates are stored directly in Sig
                        -- there is no need to call embedSig recusively
                        then FunD
                            ( mkName "embedSig" )
                            [ Clause
                                []
                                ( NormalB $ ConE $ mkName $ "Sig_"++nameBase algName
                                            ++"_"++nameBase predClass
                                            ++"_"++predType2str predType
                                )
                                []
                            ]
                        -- non-parent predicates must be embedded in the Sig
                        -- with a recusive call to embedSig
                        else FunD
                            ( mkName "embedSig" )
                            [ Clause
                                [ SigP
                                    ( VarP $ mkName "s" )
                                    ( AppT
                                        ( AppT
                                            ( AppT
                                                ( ConT $ mkName "Sig" )
                                                ( ConT predClass
                                                )
                                            )
                                            ( pred2tag
                                                PromotedNilT
                                                ( getReturnType sigType )
                                            )
                                        )
                                        ( VarT varName )
                                    )
                                ]
                                ( NormalB $ AppE
                                    ( ConE $ mkName $ "Sig_"++nameBase algName
                                        ++"_"++nameBase parentClass
                                        ++"_"++predType2str parentType
                                    )
                                    ( SigE
                                        ( AppE
                                            ( VarE $ mkName "embedSig" )
                                            ( VarE $ mkName "s" )
                                        )
                                        ( AppT
                                            ( AppT
                                                ( AppT
                                                    ( ConT $ mkName "Sig" )
                                                    ( ConT parentClass )
                                                )
                                                ( case parentType of
                                                    (VarT _) -> pred2tag
                                                        ( pred2tag PromotedNilT predType )
                                                        ( getReturnType sigType )
                                                    _ -> typeListInit $ pred2tag
                                                        ( pred2tag PromotedNilT predType )
                                                        ( getReturnType sigType )
                                                )
                                            )
                                            ( VarT varName )
                                        )
                                    )
                                )
                                []
                            ]
                    , if parent==thisPred
                        -- parent predicates are stored directly in Sig
                        -- there is no need to call unsafeExtractSig
                        then FunD
                            ( mkName "unsafeExtractSig" )
                            [ Clause
                                [ ConP
                                    ( mkName $ "Sig_"++nameBase algName
                                                ++"_"++nameBase predClass
                                                ++"_"++predType2str predType
                                    )
                                    [ VarP $ mkName "s" ]
                                ]
                                ( NormalB $ AppE
                                    ( AppE
                                        ( VarE $ mkName "unsafeCoerceSigTag" )
                                        ( SigE
                                            ( ConE $ mkName "Proxy" )
                                            ( AppT
                                                ( ConT $ mkName "Proxy" )
                                                ( pred2tag PromotedNilT $ getReturnType sigType )
                                            )
                                        )
                                    )
                                    ( VarE $ mkName "s" )
                                )
                               []
                            ]
                        -- non-parent predicates must be embedded in the Sig
                        -- with a recusive call to unsafeExtractSig
                        else FunD
                            ( mkName "unsafeExtractSig" )
                            [ Clause
                                [ ConP
                                    ( mkName $ "Sig_"++nameBase algName
                                                ++"_"++nameBase parentClass
                                                ++"_"++predType2str parentType
                                    )
                                    [ VarP $ mkName "s" ]
                                ]
                                ( NormalB $ AppE
                                    ( VarE $ mkName "unsafeExtractSig" )
                                    ( AppE
                                        ( AppE
                                            ( VarE $ mkName "unsafeCoerceSigTag" )
                                            ( SigE
                                                ( ConE $ mkName "Proxy" )
                                                ( AppT
                                                    ( ConT $ mkName "Proxy" )
                                                    ( case parentType of
                                                        (VarT _) -> pred2tag
                                                            ( pred2tag PromotedNilT predType )
                                                            ( getReturnType sigType )
                                                        _ -> typeListInit $ pred2tag
                                                            ( pred2tag PromotedNilT predType )
                                                            ( getReturnType sigType )
                                                    )
                                                )
                                            )
                                        )
                                        ( VarE $ mkName "s" )
                                    )
                                )
                                []
                            ]
                    ]
                | SigD _ sigType <- SigD undefined (VarT varName):decs
                ]
            | PredInfo
                (AppT (ConT predClass) predType)
                (ClassI (ClassD _ _ _ _ decs) _)
                (Just parent@(AppT (ConT parentClass) parentType))
                <- allcxt
            ]

    return $ ats ++ instViews ++ {-patSyns ++-} [instFAlgebra,instShow,instShowOverlap,instFree]

predType2str :: Pred -> String
predType2str (ConT t) = nameBase t
predType2str (AppT a1 a2) = predType2str a1 ++ "_" ++ predType2str a2
predType2str _ = ""

pred2strList :: Pred -> [String]
pred2strList (AppT (ConT n) t) = ("T"++nameBase n):pred2strList t
pred2strList _ = []

pred2tag :: Pred -> Pred -> TH.Type
pred2tag s t = foldr (\a b -> AppT (AppT PromotedConsT a) b) s $ go t
    where
        go (AppT a1 a2) = go a1 ++ go a2
        go (ConT t) = [ConT $ mkName $ "T"++nameBase t]
        go _ = []

cons2consTag :: TH.Type -> TH.Type
cons2consTag PromotedConsT = ConT $ mkName "ConsTag"
cons2consTag (AppT t1 t2) = AppT (cons2consTag t1) (cons2consTag t2)
cons2consTag t = t

pred2tagSingleton :: Pred -> TH.Type
pred2tagSingleton t = case pred2tag PromotedNilT t of
    (AppT (AppT PromotedConsT t) PromotedNilT) -> t

typeListTail :: TH.Type -> TH.Type
typeListTail (AppT (AppT PromotedConsT _) t) = t

typeListInit :: TH.Type -> TH.Type
typeListInit (AppT (AppT PromotedConsT t ) PromotedNilT) = PromotedNilT
typeListInit (AppT (AppT PromotedConsT t1) t2          ) = AppT (AppT PromotedConsT t1) $ typeListInit t2

typeListHead :: TH.Type -> TH.Type
typeListHead (AppT (AppT PromotedConsT t) _) = t

subAllVars :: TH.Type -> TH.Type -> TH.Type
subAllVars e = go
    where
        go (VarT _) = e
        go (AppT t1 t2) = AppT (go t1) (go t2)
        go t = t

renameVars :: TH.Type -> TH.Type
renameVars = go
    where
        go (VarT n) = VarT $ mkName $ nameBase n
        go (AppT t1 t2) = AppT (go t1) (go t2)
        go t = t

mkProxyE :: TH.Type -> Exp
mkProxyE t = SigE
    ( ConE $ mkName "Proxy" )
    ( AppT (ConT $ mkName "Proxy") t)

-- | Converts a type of the form
--
-- > Scalar (Scalar (Scalar a)))
--
-- into
--
-- > TScalar ': TScalar ': TScalar ': t
type2tag :: TH.Type -> TH.Type
type2tag (AppT (ConT n) t) = AppT
    ( AppT
        ( ConT $ mkName "ConsTag" )
        ( ConT $ mkName $ "T"++nameBase n )
    )
    ( type2tag t )
type2tag _ = VarT $ mkName "t"

-- | Stores all the information we'll need about a predicate
data PredInfo = PredInfo
    { predSig    :: Pred
    , predReify  :: Info
    , predHost   :: Maybe Pred
    }
    deriving (Eq,Show)

depthSameAppT :: TH.Type -> Int
depthSameAppT (AppT t1 t2) = go 1 t2
    where
        go i (AppT t1' t2') = if t1==t1'
            then go (i+1) t2'
            else i
        go i _ = i
depthSameAppT _ = 0

-- | Given a predicate that represents a class/tag combination,
-- recursively list all super predicates
superPredicates :: Pred -> Q [PredInfo]
superPredicates (ForallT _ _ t) = superPredicates t
superPredicates rootPred@(AppT (ConT predClass) _) = {-trace "" $ trace "superPred" $-} do
    qinfo <- reify predClass
    go [] $ PredInfo rootPred qinfo Nothing
    where

        -- FIXME
        stopRecursion :: TH.Type -> Q Bool
        stopRecursion (AppT _ (AppT (ConT c) t)) = do
            idemp <- isIdempotent c
--             return $ idemp && depthSameAppT (AppT (ConT c) t) > 2
            return $ depthSameAppT (AppT (ConT c) t) > 2
        stopRecursion _ = return False

        go :: [PredInfo] -> PredInfo -> Q [PredInfo]
        go prevCxt predInfo@(PredInfo (AppT (ConT predClass) predType) _ _) = do
--             trace ("predClass="++nameBase predClass++"; predType="++show predType) $ return ()
            stop <- stopRecursion (predSig predInfo)
            if stop
                then return prevCxt
                else do
                    qinfo <- reify predClass
                    cxt <- case qinfo of
                        ClassI (ClassD cxt _ [_] _ _) _ -> return cxt
                        _ -> error $ "superPredicates called on "
                            ++show predClass
                            ++", which is not a class of kind `Type -> Constraint`"
                    newCxt <- mapM (go [] {-$ predInfo:prevCxt-})
                        $ filter (`notElem` prevCxt)
                        $ map (\sig -> PredInfo sig undefined $ if predHost predInfo==Nothing || predHost predInfo==Just rootPred
                            then Just $ predSig predInfo
                            else predHost predInfo
                            )
                        $ map (subPred predType) cxt
                    return
                        $ nub
                        $ predInfo { predReify=qinfo }:prevCxt++concat newCxt
        go prevCxt _ = return prevCxt

        -- When the go function recurses,
        -- we need to remember what layer of tags we've already seen.
        -- This function substitutes those tags into the predicate.
        subPred :: Pred -> Pred -> Pred
        subPred predType' (AppT (ConT predClass) predType) = AppT (ConT predClass) $ go predType
            where
                go (AppT t1 t2) = AppT t1 $ go t2
                go (VarT t) = predType'
                go t = t
        subPred p t = t -- FIXME?
