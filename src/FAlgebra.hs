{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilyDependencies #-}

{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

module FAlgebra
    where

import Prelude
import Control.Monad
import Data.Foldable
import Data.List
import Data.Maybe
import Data.Typeable

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

type AT = Type

type family App (t::k) (a::Type) ::  Type
type instance App '[]           a = a
type instance App ((x::AT)':xs) a = App x (App xs a)

type family TypeConstraints (t::[AT]) (a::Type) :: Constraint


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
    -> App t (App s a)
    -> App (t `Snoc` s) a
appCoerce _ _ _ = unsafeCoerce

sigCoerce
    :: Proxy t
    -> Proxy s
    -> Proxy a
    -> Sig alg t (App (t `Snoc` s) a)
    -> Sig alg t (App  t (App s a))
sigCoerce _ _ _ = unsafeCoerce

runSigSnoc :: forall proxy alg a t u.
    ( FAlgebra alg
    , alg (App u a)
    ) => Proxy u
--       -> Proxy u
      -> Proxy a
      -> Sig alg t (App (t `Snoc` u) a)
      -> App (t `Snoc` u) a
runSigSnoc ps pa u
    = appCoerce pt ps pa $ runSig (Proxy::Proxy (App u a)) $ sigCoerce pt ps pa u
    where
        pt = Proxy :: Proxy t

type family Init (xs::[a]) where
    Init (x ': '[]) = '[]
    Init (x ': xs ) = x ': Init xs

runSigTagSnoc :: forall proxy alg a s ttt t u.
    ( FAlgebra alg
    , alg (App u a)
    ) => Proxy u
      -> Proxy (s::AT)
      -> Proxy (t::[AT])
      -> Proxy a
      -> Sig alg ttt (App t a)
      -> App s (App t a)
runSigTagSnoc pu ps pt pa s
    = unsafeCoerce $ runSigTag
        (Proxy::Proxy (App u a))
        (unsafeCoerce s :: Sig alg (s ': Init t) (App (Init t) (App u a)))

unsafeCoerceSigTag :: proxy t' -> Sig alg t a -> Sig alg t' a
unsafeCoerceSigTag _ = unsafeCoerce

----------------------------------------

data Free (f::[AT]->Type->Type) (t::[AT]) (a::Type) where
    FreeTag  :: TypeConstraints t a => f (s ': t) (Free f t a)  -> Free f (s ': t) a
    Free     :: TypeConstraints t a => f       t  (Free f t a)  -> Free f       t  a
    Pure     :: App t a -> Free f t a

instance
    ( Show      (App t a)
    , Show      (f t (Free f t a))
    , ShowUntag (f t (Free f t a))
    ) => Show (Free f t a)
        where
    show (FreeTag     f) = "("++show f++")"
    show (Free        f) = "("++show f++")"
    show (Pure        a) = show a

type family ShowUntag (f::Type) :: Constraint where
    ShowUntag (f (s ':  t) (Free f (s ':  t) a))  = Show (f (s ':  t) (Free f          t  a))
    ShowUntag a = ()

eval :: forall alg t a.
    ( FAlgebra alg
    , alg a
    ) => Free (Sig alg) t a -> App t a
eval (Pure    a) = a
eval (Free    s) = runSig    (Proxy::Proxy a) $ mape eval s
eval (FreeTag s) = runSigTag (Proxy::Proxy a) $ mape eval s

----------------------------------------

class FAlgebra (alg::Type->Constraint) where
    data Sig alg (t::[AT]) a

    runSigTag :: alg a => proxy a -> Sig alg (s ':  t) (App t a) -> App (s ':  t) a
    runSig    :: alg a => proxy a -> Sig alg        t  (App t a) -> App        t  a

    mape :: (TypeConstraints t' a)
         => (forall s. Free (Sig alg') s a -> App s a)
         -> Sig alg t (Free (Sig alg') t' a)
         -> Sig alg t (App t' a)

----------------------------------------

class (FAlgebra alg1, FAlgebra alg2) => View alg1 t1 alg2 t2 where
    embedSig         :: Sig alg1       t1  a -> Sig alg2       t2  a
    unsafeExtractSig :: Sig alg2       t2  a -> Sig alg1       t1  a

embedSigTag :: View alg1 (t ': t1) alg2 (t ': t2) => Sig alg1 (t ': t1) a -> Sig alg2 (t ': t2) a
embedSigTag = embedSig

instance FAlgebra alg => View alg t alg t where
    embedSig = id
    unsafeExtractSig = id

--------------------------------------------------------------------------------

-- | Constructs the needed declarations for a type family
mkAT :: Name -> Q [Dec]
mkAT atName = do

    -- validate input
    qinfo <- reify atName
    case qinfo of
        FamilyI (OpenTypeFamilyD (TypeFamilyHead _ [_] _ _)) _ -> return ()
        _ -> error $ "mkAt called on "
            ++show atName
            ++", which is not an open type family of kind `Type -> Type`"

    -- common names
    let tagName = mkName $ "T"++nameBase atName
        varName = mkName "a"

    -- construct the data Tag
    let decT = DataD
            []
            tagName
            []
            Nothing
            [NormalC tagName []]
            []

    -- construct the App instance
    let instApp = TySynInstD
            ( mkName "App" )
            ( TySynEqn
                [ ConT tagName, VarT varName ]
                ( AppT
                    ( ConT atName )
                    ( VarT varName )
                )
            )

    -- FIXME:
    -- We need to add the TypeConstraints instance here

    return [decT, instApp]

mkFAlgebra :: Name -> Q [Dec]
mkFAlgebra algName = do

    -- validate input and extract the class functions
    qinfo <- reify algName
    (cxt,decs) <- case qinfo of
        ClassI (ClassD cxt _ [_] _ decs) _ -> return (cxt,decs)
        _ -> error $ "mkFAlgebra called on "
            ++show algName
            ++", which is not a class of kind `Type -> Constraint`"

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
        [ mkAT atName
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
                        ( predType2tagType PromotedNilT $ getReturnType $ subForall varName sigType )
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
                ( mkName "mape" )
                (
                    -- for each function constructor
                    [ Clause
                        [ VarP $ mkName "f"
                        , ConP
                            ( mkName $ "Sig_" ++ renameClassMethod sigName )
                            ( map VarP $ genericArgs sigType )
                        ]
                        ( NormalB $ foldr
                            (\a b -> AppE
                                b
                                ( AppE
                                    ( VarE $ mkName "f")
                                    ( VarE $ a)
                                )
                            )
                            ( ConE $ mkName $ "Sig_" ++ renameClassMethod sigName )
                            ( reverse $ genericArgs sigType )
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
                                        ( VarE $ mkName "mape" )
                                        ( VarE $ mkName "f" )
                                    )
                                    ( VarE $ mkName "s" )
                                )
                            )
                        )
                        []
                    | AppT (ConT predClass) predType <- cxt
                    ]
                )
            , FunD
                ( mkName "runSigTag" )
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
                                        ( ConT $ mkName "App" )
                                        ( VarT $ mkName "t" )
                                    )
                                    ( VarT $ mkName "a" )
                                )
                            )
                        ]
                        ( NormalB $ case predType of
                            (VarT _) -> AppE
                                ( AppE
                                    ( VarE $ mkName "runSigTag" )
                                    ( case predType of
                                        (VarT _) -> VarE $ mkName "p"
                                        _        -> SigE
                                            ( ConE $ mkName "Proxy" )
                                            ( AppT
                                                ( ConT $ mkName "Proxy" )
                                                ( subAllVars varName predType )
                                            )
                                    )
                                )
                                ( VarE $ mkName "s" )
                            _ -> AppE
                                ( AppE
                                    ( AppE
                                        ( AppE
                                            ( AppE
                                                ( VarE $ mkName "runSigTagSnoc" )
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
                            ( LitE $ StringL $ "runSigTag ("++nameBase algName++"): this should never happen" )
                        )
                        []
                    ]
                )
            , FunD
                ( mkName "runSig" )
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
                                    ( VarE $ mkName "runSig" )
                                    ( VarE $ mkName "p" )
                                )
                                ( VarE $ mkName "s" )

                            _ -> AppE
                                ( AppE
                                    ( AppE
                                        ( VarE $ mkName "runSigSnoc" )
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
                            ( LitE $ StringL $ "runSig ("++nameBase algName++"): this should never happen" )
                        )
                        []
                    ]
                )

--             , TySynInstD
--                 ( mkName $ "ParentClasses" )
--                 ( TySynEqn
--                     [ ConT $ algName ]
--                     ( foldl (\b a -> AppT (AppT PromotedConsT (ConT a)) b) PromotedNilT parentClasses )
--                 )
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
                (nub $ concat $ concat $
                [   [   [ AppT
                            ( ConT $ mkName "Show" )
                            ( subAllVars varName t )
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
                )
            ]

    -- construct the `View alg '[] alg' t => alg (Free (Sig alg') t a)` instance
    let algName' = mkName "alg'"
    let instFree = InstanceD
            Nothing
            ( nub $ concat $
                [   [ AppT
                        ( AppT
                            ( AppT
                                ( AppT
                                    ( ConT $ mkName "View" )
                                    ( ConT predClass )
                                )
                                ( predType2tagType PromotedNilT $ getReturnType sigType )
                            )
                            ( VarT algName' )
                        )
                        ( predType2tagType
                            ( predType2tagType (VarT tagName) predType )
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
            ( AppT
                ( ConT algName )
                ( AppT
                    ( AppT
                        ( AppT
                            ( ConT $ mkName "Free" )
                            ( AppT
                                ( ConT $ mkName "Sig" )
                                ( VarT algName' )
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
                                    ( VarT algName' )
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
                                    ( VarT algName' )
                                )
                            )
                            ( AppT
                                ( AppT
                                    PromotedConsT
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
                                ( ConE $ mkName "Free" )
                                ( AppE
                                    ( VarE $ mkName "embedSig" )
                                    ( foldl AppE (ConE $ mkName $ "Sig_"++renameClassMethod sigName)
                                        $ map VarE $ genericArgs sigType
                                    )
                                )
                            _ -> AppE
                                ( ConE $ mkName "FreeTag")
                                ( AppE
                                    ( VarE $ mkName "embedSigTag" )
                                    ( foldl AppE (ConE $ mkName $ "Sig_"++renameClassMethod sigName)
                                        $ map VarE $ genericArgs sigType
                                    )
                                )
                        )
                        []
                    ]
                | SigD sigName sigType <- decs
                ]
            )

    -- construct the `View alg alg'` instances
    let instViews = nub $ concat
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
                                ( predType2tagType
                                    PromotedNilT
                                    ( getReturnType sigType )
                                )
                            )
                            ( ConT algName )
                        )
                        ( predType2tagType
                            ( predType2tagType PromotedNilT predType )
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
                                            ( predType2tagType
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
                                                    (VarT _) -> predType2tagType
                                                        ( predType2tagType PromotedNilT predType )
                                                        ( getReturnType sigType )
                                                    _ -> typeListInit $ predType2tagType
                                                        ( predType2tagType PromotedNilT predType )
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
                                                ( predType2tagType PromotedNilT $ getReturnType sigType )
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
                                                        (VarT _) -> predType2tagType
                                                            ( predType2tagType PromotedNilT predType )
                                                            ( getReturnType sigType )
                                                        _ -> typeListInit $ predType2tagType
                                                            ( predType2tagType PromotedNilT predType )
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

    return $ ats ++ instViews ++ [instFAlgebra,instShow,instShowOverlap,instFree]

predType2str :: Pred -> String
predType2str (ConT t) = nameBase t
predType2str (AppT a1 a2) = predType2str a1 ++ "_" ++ predType2str a2
predType2str _ = ""

predType2tagType :: Pred -> Pred -> TH.Type
predType2tagType s t = foldr (\a b -> AppT (AppT PromotedConsT a) b) s $ go t
    where
        go (AppT a1 a2) = go a1 ++ go a2
        go (ConT t) = [ConT $ mkName $ "T"++nameBase t]
        go _ = []

pred2tagSingleton :: Pred -> TH.Type
pred2tagSingleton t = case predType2tagType PromotedNilT t of
    (AppT (AppT PromotedConsT t) PromotedNilT) -> t

typeListTail :: TH.Type -> TH.Type
typeListTail (AppT (AppT PromotedConsT _) t) = t

typeListInit :: TH.Type -> TH.Type
typeListInit (AppT (AppT PromotedConsT t ) PromotedNilT) = PromotedNilT
typeListInit (AppT (AppT PromotedConsT t1) t2          ) = AppT (AppT PromotedConsT t1) $ typeListInit t2

typeListHead :: TH.Type -> TH.Type
typeListHead (AppT (AppT PromotedConsT t) _) = t

subAllVars :: Name -> TH.Type -> TH.Type
subAllVars varName = go
    where
        go (VarT _) = VarT varName
        go (AppT t1 t2) = AppT (go t1) (go t2)
        go t = t

mkProxyE :: TH.Type -> Exp
mkProxyE t = SigE
    ( ConE $ mkName "Proxy" )
    ( AppT (ConT $ mkName "Proxy") t)

-- | Stores all the information we'll need about a predicate
data PredInfo = PredInfo
    { predSig    :: Pred
    , predReify  :: Info
    , predHost   :: Maybe Pred
    }
    deriving (Eq,Show)

-- | Given a predicate that represents a class/tag combination,
-- recursively list all super predicates
superPredicates :: Pred -> Q [PredInfo]
superPredicates rootPred@(AppT (ConT predClass) _) = do
    qinfo <- reify predClass
    go [] $ PredInfo rootPred qinfo Nothing
    where

        go :: [PredInfo] -> PredInfo -> Q [PredInfo]
        go prevCxt predInfo = do
            let pred@(AppT (ConT predClass) predType) = predSig predInfo
            qinfo <- reify predClass
            cxt <- case qinfo of
                ClassI (ClassD cxt _ [_] _ _) _ -> return cxt
                _ -> error $ "superPredicates called on "
                    ++show predClass
                    ++", which is not a class of kind `Type -> Constraint`"
            newCxt <- mapM (go [])
                $ filter (`notElem` prevCxt)
                $ map (\sig -> PredInfo sig undefined $ if predHost predInfo==Nothing || predHost predInfo==Just rootPred
                    then Just pred
                    else predHost predInfo
                    )
                $ map (subPred predType) cxt
            return
                $ nub
                $ predInfo { predReify=qinfo }:prevCxt++concat newCxt

        -- When the go function recurses,
        -- we need to remember what layer of tags we've already seen.
        -- This function substitutes those tags into the predicate.
        subPred :: Pred -> Pred -> Pred
        subPred predType' (AppT (ConT predClass) predType) = AppT (ConT predClass) $ go predType
            where
                go (AppT t1 t2) = AppT t1 $ go t2
                go (VarT t) = predType'
                go t = t
