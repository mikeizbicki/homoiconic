module Homoiconic.Homogeneous.TH
    where

import Prelude
import Control.Monad
import Data.List
import Data.Foldable
import Data.Typeable

import Data.Kind
import GHC.Exts hiding (IsList(..))

import Homoiconic.Common.TH
import Language.Haskell.TH hiding (Type)
import qualified Language.Haskell.TH as TH

--------------------------------------------------------------------------------

-- | Constructs instances for FAlgebra and related classes.
mkFAlgebra :: Name -> Q [Dec]
mkFAlgebra algName = do

    -- validate input and extract the class functions
    qinfo <- reify algName
    rawdecs <- case qinfo of
        ClassI (ClassD cxt _ [_] _ decs) _ -> return decs
        _ -> error $ "mkFAlgebra called on "
            ++show algName
            ++", which is not a class of kind `Type -> Constraint`"

    -- remove functions from decsraw that we can't handle
    let go x = case x of
            SigD _ sigType -> if not $ isVarT $ getReturnType sigType
                then False
                else True -- and $ map isVarT $ getArgs sigType
    let decs = filter go rawdecs

    -- common variables we'll need later
    let varName = mkName "a"
    parentClasses <- listParentClasses algName
    superClasses <- listSuperClasses algName
    superClassesWithParents <- listSuperClassesWithParents algName

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
                [ ConT algName, VarT varName ]
                Nothing
                (
                    -- create a constructor for each member function
                    [ NormalC
                        ( mkName $ "Sig_" ++ renameClassMethod sigName )
                        ( map
                            (Bang NoSourceUnpackedness NoSourceStrictness,)
                            (getArgs $ subForall varName sigType) )
                        | SigD sigName sigType <- decs
                    ]
                    ++
                    -- create a constructor for each parent class to hold their signatures
                    [ NormalC
                        ( mkName $ "Sig_"++nameBase algName++"_"++nameBase parentClass)
                        [ ( Bang NoSourceUnpackedness SourceStrict
                          , AppT
                            ( AppT
                                ( ConT $ mkName "Sig" )
                                ( ConT parentClass )
                            )
                            ( VarT varName )
                          )
                        ]
                        | parentClass <- parentClasses
                    ]
                )
                []

            , FunD
                ( mkName "runSig" )
                (
                    -- evaluate functions
                    [ Clause
                        [ ConP
                            ( mkName $ "Sig_" ++ renameClassMethod sigName )
                            ( map VarP $ genericArgs sigType )
                        ]
                        ( NormalB $ foldl AppE
                            ( VarE sigName )
                            ( map VarE $ genericArgs sigType )
                        )
                        []
                        | SigD sigName sigType <- decs
                    ]
                    ++
                    -- evaluate nested constructors
                    [ Clause
                        [ ConP
                            ( mkName $ "Sig_"++nameBase algName++"_"++nameBase parentClass )
                            [ VarP $ mkName $ "s" ]
                        ]
                        ( NormalB $ AppE
                            ( VarE $ mkName "runSig" )
                            ( VarE $ mkName "s" )
                        )
                        []
                        | parentClass <- parentClasses
                    ]
                    ++
                    -- ensure that there's always at least one clause
                    [ Clause
                        [ VarP $ mkName "_" ]
                        ( NormalB $ AppE
                            ( VarE $ mkName "error" )
                            ( LitE $ StringL $ "runSig called on "++nameBase algName++" which has no homogeneous class methods" )
                        )
                        []
                    ]
                )

            , TySynInstD
                ( mkName $ "ParentClasses" )
                ( TySynEqn
                    [ ConT $ algName ]
                    ( foldl (\b a -> AppT (AppT PromotedConsT (ConT a)) b) PromotedNilT parentClasses )
                )
            ]

    -- deriving instance (Eq a) => Eq (Sig alg a)
    let instEqSig = StandaloneDerivD Nothing
            [ AppT
                ( ConT $ mkName "Eq" )
                ( VarT $ mkName "a" )
            ]
            ( AppT
                ( ConT $ mkName "Eq" )
                ( AppT
                    ( AppT
                        ( ConT $ mkName "Sig" )
                        ( ConT $ algName )
                    )
                    ( VarT $ mkName "a" )
                )
            )

    -- construct the `Functor (Sig alg)` instance
    let instFunctor = InstanceD
            Nothing
            []
            ( AppT
                ( ConT $ mkName "Functor")
                ( AppT
                    ( ConT $ mkName "Sig" )
                    ( ConT $ algName )
                )
            )
            [ FunD
                ( mkName "fmap" )
                (
                    -- map over constructors for member functions
                    [ Clause
                        [ VarP $ mkName "f"
                        , ConP
                            ( mkName $ "Sig_" ++ renameClassMethod sigName )
                            ( map VarP $ genericArgs sigType )
                        ]
                        ( NormalB $ foldl AppE (ConE (mkName $ "Sig_" ++ renameClassMethod sigName))
                            [ if isVarT argType
                                then AppE
                                    ( VarE $ mkName "f" )
                                    ( VarE $ argName )
                                else VarE argName
                            | (argName,argType) <- zip (genericArgs sigType) (getArgs sigType)
                            ]
                        )
                        []
                        | SigD sigName sigType <- decs
                    ]
                    ++
                    -- map over embedded constructors
                    [ Clause
                        [ VarP $ mkName "f"
                        , ConP
                            ( mkName $ "Sig_"++nameBase algName++"_"++nameBase parentClass )
                            [ VarP $ mkName "s" ]
                        ]
                        ( NormalB $ AppE
                            ( ConE $ mkName $ "Sig_"++nameBase algName++"_"++nameBase parentClass )
                            ( AppE
                                ( AppE
                                    ( VarE $ mkName "fmap" )
                                    ( VarE $ mkName "f" )
                                )
                                ( VarE $ mkName "s" )
                            )
                        )
                        []
                        | parentClass <- parentClasses
                    ]
                    ++
                    -- ensure that there's always at least one clause
                    [ Clause
                        [ VarP $ mkName "f", VarP $ mkName "a" ]
                        ( NormalB $ AppE
                            ( VarE $ mkName "error" )
                            ( LitE $ StringL $ "fmap called on Sig "++nameBase algName++" which has no homogeneous class methods" )
                        )
                        []
                    ]
                )
            ]

    -- construct the `Foldable (Sig alg)` instance
    let instFoldable = InstanceD
            Nothing
            []
            ( AppT
                ( ConT $ mkName "Foldable" )
                ( AppT
                    ( ConT $ mkName "Sig" )
                    ( ConT algName )
                )
            )
            [ FunD
                ( mkName "foldr" )
                (
                    -- fold over constructors for member functions
                    [ Clause
                        [ VarP $ mkName "f"
                        , VarP $ mkName "b"
                        , ConP
                            ( mkName $ "Sig_" ++ renameClassMethod sigName )
                            ( map VarP $ genericArgs sigType )
                        ]
                        ( NormalB $ foldl
                            (\a b -> AppE
                                ( AppE
                                    ( VarE $ mkName "f" )
                                    b
                                )
                                a
                            )
                            ( VarE $ mkName "b" )
                            ( reverse
                                $ map (VarE . fst)
                                $ filter (isVarT . snd)
                                $ zip (genericArgs sigType) (getArgs sigType)
                            )
                        )
                        []
                        | SigD sigName sigType <- decs
                    ]
                    ++
                    -- fold over embedded constructors
                    [ Clause
                        [ VarP $ mkName "f"
                        , VarP $ mkName "b"
                        , ConP
                            ( mkName $ "Sig_"++nameBase algName++"_"++nameBase parentClass )
                            [ VarP $ mkName "s" ]
                        ]
                        ( NormalB $ AppE
                            ( AppE
                                ( AppE
                                    ( VarE $ mkName "foldr" )
                                    ( VarE $ mkName "f" )
                                )
                                ( VarE $ mkName "b" )
                            )
                            ( VarE $ mkName "s" )
                        )
                        []
                        | parentClass <- parentClasses
                    ]
                    ++
                    -- ensure that there's always at least one clause
                    [ Clause
                        [ VarP $ mkName "f", VarP $ mkName "b", VarP $ mkName "ta" ]
                        ( NormalB $ AppE
                            ( VarE $ mkName "error" )
                            ( LitE $ StringL $ "foldr called on Sig "++nameBase algName++" which has no homogeneous class methods" )
                        )
                        []
                    ]
                )
            ]

    -- construct the `Show a => Show (Sig alg a)` instance
    let instShow = InstanceD
            Nothing
            [ AppT
                ( ConT $ mkName "Show" )
                ( VarT varName )
            ]
            ( AppT
                ( ConT $ mkName "Show" )
                ( AppT
                    ( AppT
                        ( ConT $ mkName "Sig" )
                        ( ConT algName )
                    )
                    ( VarT $ varName )
                )
            )
            [ FunD
                ( mkName "show" )
                (
                    -- predicate constructors
                    [ Clause
                        [ ConP
                            ( mkName $ "Sig_"++nameBase algName++"_"++nameBase parentClass)
                            [ VarP $ mkName "s" ]
                        ]
                        ( NormalB $ AppE
                            ( VarE $ mkName "show" )
                            ( VarE $ mkName "s" )
                        )
                        []
                        | parentClass <- parentClasses
                    ]
                    ++
                    -- function constructors
                    [ Clause
                        [ ConP
                            ( mkName $ "Sig_" ++ renameClassMethod sigName )
                            ( map VarP $ genericArgs sigType )
                        ]
                        ( if isOperator (nameBase sigName)

                            -- if we're an operator, then there's exactly two arguments named e0, e1;
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
                    -- ensure that there's always at least one clause
                    [ Clause
                        [ VarP $ mkName "f" ]
                        ( NormalB $ AppE
                            ( VarE $ mkName "error" )
                            ( LitE $ StringL $ "show called on Sig "++nameBase algName++" which has no homogeneous class methods" )
                        )
                        []
                    ]
                )
            ]

    -- construct the `View alg alg' => alg (Free (Sig alg') a)` instance
    let algName' = mkName "alg'"
    let instHomFree = InstanceD
            Nothing
            (
                -- FIXME: this constraint is a hack so that we can make Ord instances
                ( if nameBase algName=="Ord" || nameBase algName=="FloatingOrd"
                    then
                        [ AppT
                            ( ConT $ mkName "Eq" )
                            ( VarT $ varName )
                        , AppT
                            ( ConT $ mkName "Eq" )
                            ( AppT
                                ( AppT
                                    ( ConT $ mkName "Sig" )
                                    ( VarT $ mkName "alg'" )
                                )
                                ( AppT
                                    ( AppT
                                        ( ConT $ mkName "Free" )
                                        ( AppT
                                            ( ConT $ mkName "Sig" )
                                            ( VarT $ mkName "alg'" )
                                        )
                                    )
                                    ( VarT $ mkName "a" )
                                )
                            )
                        ]
                    else []
                )
                ++
                -- all the View constraints
                [ AppT
                    ( AppT
                        ( ConT $ mkName "View" )
                        ( ConT n )
                    )
                    ( VarT algName' )
                | n <- algName:superClasses
                ]
            )
            ( AppT
                ( ConT algName )
                ( AppT
                    ( AppT
                        ( ConT $ mkName "Free" )
                        ( AppT
                            ( ConT $ mkName "Sig" )
                            ( VarT algName' )
                        )
                    )
                    ( VarT varName )
                )
            )
            [ FunD
                sigName
                [ Clause
                    ( map VarP $ genericArgs sigType )
                    ( NormalB $ AppE
                        ( ConE $ mkName "Free" )
                        ( AppE
                            ( VarE $ mkName "embedSig" )
                            ( foldl AppE
                                ( ConE $ mkName $ "Sig_"++renameClassMethod sigName )
                                ( map VarE $ genericArgs sigType )
                            )
                        )
                    )
                    []
                ]
            | SigD sigName sigType <- decs
            ]

    -- construct the `View alg alg'` instances
    let instHomViews =

            -- parent classes are stored directly in the Sig type
            [ InstanceD
                Nothing
                []
                ( AppT
                    ( AppT
                        ( ConT $ mkName "View" )
                        ( ConT superClass )
                    )
                    ( ConT algName )
                )
                [ FunD
                    ( mkName "embedSig" )
                    [ Clause
                        []
                        ( NormalB $ ConE $ mkName $ "Sig_"++nameBase algName++"_"++nameBase superClass )
                        []
                    ]
                , FunD
                    ( mkName "unsafeExtractSig" )
                    [ Clause
                        [ ConP
                            ( mkName $ "Sig_"++nameBase algName++"_"++nameBase superClass )
                            [ VarP $ mkName "s" ]
                        ]
                        ( NormalB $ VarE $ mkName "s" )
                        []
                    ]
                ]
            | superClass <- parentClasses
            ]
            ++
            -- ancestors that are not parents must be accessed via a parent
            [ InstanceD
                Nothing
                []
                ( AppT
                    ( AppT
                        ( ConT $ mkName "View" )
                        ( ConT superClass )
                    )
                    ( ConT algName )
                )
                [ FunD
                    ( mkName "embedSig" )
                    [ Clause
                        [ VarP $ mkName "s" ]
                        ( NormalB $ AppE
                            ( ConE $ mkName $ "Sig_"++nameBase algName++"_"++nameBase parentClass )
                            ( AppE
                                ( VarE $ mkName "embedSig" )
                                ( VarE $ mkName "s" )
                            )
                        )
                        []
                    ]
                , FunD
                    ( mkName "unsafeExtractSig" )
                    [ Clause
                        [ ConP
                            ( mkName $ "Sig_"++nameBase algName++"_"++nameBase parentClass )
                            [ VarP $ mkName "s" ]
                        ]
                        ( NormalB $ AppE
                            ( VarE $ mkName "unsafeExtractSig" )
                            ( VarE $ mkName "s" )
                        )
                        []
                    ]
                ]
            | (parentClass,superClass) <- superClassesWithParents
            ]

    -- construct pattern synonyms
    let patSyns =
#if __GHC__GLASGOW__ < 801
            []
#else
            [ PatSynD
                ( mkName $ "AST_" ++ renameClassMethod sigName )
                ( PrefixPatSyn $ genericArgs sigType )
                ( ExplBidir
                    [ Clause
                        ( map VarP $ genericArgs sigType )
                        ( NormalB $ AppE
                            ( ConE $ mkName "Free" )
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
                    ( mkName "Free" )
                    [ ViewP
                        ( VarE $ mkName "unsafeExtractSig" )
                        ( ConP
                            ( mkName $ "Sig_" ++ renameClassMethod sigName )
                            ( map VarP $ genericArgs sigType )
                        )
                    ]
                )
            | SigD sigName sigType <- decs
            ]
#endif

    -- return the instances
    return $ [instFAlgebra, instEqSig,instFunctor,instFoldable,instShow,instHomFree] ++ instHomViews ++ patSyns
