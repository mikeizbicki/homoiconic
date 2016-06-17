{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilyDependencies #-}

{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

module Heterogeneous.TH
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

import Common.TH
import Language.Haskell.TH hiding (Type)
import qualified Language.Haskell.TH as TH

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

    -- construct the AppTags instance
    let instApp = TySynInstD
            ( mkName "AppTag" )
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
    (cxt,rawdecs) <- case qinfo of
        ClassI (ClassD cxt _ [_] _ decs) _ -> return (cxt,decs)
        _ -> error $ "mkFAlgebra called on "
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
                [ ( Bang NoSourceUnpackedness SourceStrict
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
--                                     ( case predType of
--                                         (VarT _)  -> VarE $ mkName "p"
--                                         otherwise -> SigE
--                                             ( ConE $ mkName "Proxy" )
--                                             ( AppT
--                                                 ( ConT $ mkName "Proxy" )
--                                                 ( subAllVars varName predType )
--                                             )
--                                     )
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
                                                        else predType2tagType (VarT tagName) a
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
                                        ( predType2tagType PromotedNilT $ getReturnType sigType )
                                    )
                                    ( VarT $ mkName "alg" )
                                )
                                ( predType2tagType (VarT tagName) $ getReturnType sigType )
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
                                                    else predType2tagType (VarT tagName) a
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
                                            else predType2tagType (VarT tagName) $ getReturnType sigType
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
                                ( subAllVars varName t )
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
                                ( ConE $ mkName "Free0" )
                                ( AppE
                                    ( VarE $ mkName "embedSig" )
                                    ( foldl AppE (ConE $ mkName $ "Sig_"++renameClassMethod sigName)
                                        $ map VarE $ genericArgs sigType
                                    )
                                )
                            _ -> AppE
                                ( ConE $ mkName "Free1")
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

    return $ ats ++ instViews ++ patSyns ++ [instFAlgebra,instShow,instShowOverlap,instFree]

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
