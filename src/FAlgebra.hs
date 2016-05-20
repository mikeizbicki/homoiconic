{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# LANGUAGE TypeInType #-}

{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

module FAlgebra
    where

import Prelude
import Control.Monad
import Data.List
import Data.Foldable
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

--------------------------------------------------------------------------------

type AT = Type

type family App (t::k) (a::Type) ::  Type
type instance App '[]           a = a
type instance App ((x::AT)':xs) a = App x (App xs a)

type family TypeConstraints (t::[AT]) (a::Type) :: Constraint

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
    allcxt <- superPredicates (AppT (ConT algName) (VarT tagName))

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
                        PromotedNilT
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
                        ( predType2tagType PromotedNilT predType )
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
--             , FunD
--                 ( mkName "runSig" )
--                 (
--                     -- evaluate functions
--                     [ let args = args2pat sigName $ getArgs $ subForall (mkName "e") sigType
--                       in Clause
--                         [ ConP ( mkName $ "Sig_" ++ renameClassMethod sigName ) args
--                         ]
--                         ( NormalB $ foldl AppE (VarE sigName) $ map (\(VarP n)->VarE n) args )
--                         []
--                         | SigD sigName sigType <- decs
--                     ]
--                     ++
--                     -- evaluate nested constructors
--                     [ Clause
--                         [ ConP
--                             ( mkName $ "Sig_"++nameBase algName++"_"++nameBase parentClass )
--                             [ VarP $ mkName $ "s" ]
--                         ]
--                         ( NormalB $ AppE
--                             ( VarE $ mkName "runSig" )
--                             ( VarE $ mkName "s" )
--                         )
--                         []
--                         | parentClass <- parentClasses
--                     ]
--                 )

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
                            [1..10]
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
                -- Show instances for predicate constructors
                [ AppT ( ConT $ mkName "Show" ) argType
                | GadtC _ [(_,argType)] _ <- consPred
                ]
                ++
                -- Show instances for constructor arguments
                ( concat $
                    [ [ AppT ( ConT $ mkName "Show" ) argType
                      | (_,argType) <- args
                      ]
                    | GadtC _ args _ <- consFunc
                    ]
                )
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
            [ AppT
                ( AppT
                    ( AppT
                        ( AppT
                            ( ConT $ mkName "View" )
                            ( ConT predClass )
                        )
                        PromotedNilT
                    )
                    ( VarT algName' )
                )
                ( predType2tagType (VarT tagName) predType )
                | AppT (ConT predClass) predType <- allcxt
            ]
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
    let instViews =

            -- parent classes are stored directly in the Sig type
            [ InstanceD
                Nothing
                []
                ( AppT
                    ( AppT
                        ( AppT
                            ( AppT
                                ( ConT $ mkName "View" )
                                ( ConT predClass )
                            )
                            PromotedNilT
                        )
                        ( ConT algName )
                    )
                    ( predType2tagType PromotedNilT predType )
                )
                [ FunD
                    ( mkName "embedSig" )
                    [ Clause
                        []
                        ( NormalB $ ConE
                            $ mkName $ "Sig_"++nameBase algName
                                        ++"_"++nameBase predClass
                                        ++"_"++predType2str predType
                        )
                        []
                    ]
                , FunD
                    ( mkName "unsafeExtractSig" )
                    [ Clause
                        [ ConP
                            ( mkName $ "Sig_"++nameBase algName
                                        ++"_"++nameBase predClass
                                        ++"_"++predType2str predType
                            )
                            [ VarP $ mkName "s" ]
                        ]
                        ( NormalB $ VarE $ mkName "s" )
                        []
                    ]
                ]
            | AppT (ConT predClass) predType <- cxt
            ]

            -- FIXME:
            -- need to add instances for non-parent predicates

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

-- | Given a predicate that represents a class/tag combination,
-- recursively list all super predicates
superPredicates :: Pred -> Q [Pred]
superPredicates = go []
    where
        go prevCxt pred@(AppT (ConT predClass) predType) = do
            qinfo <- reify predClass
            cxt <- case qinfo of
                ClassI (ClassD cxt _ [_] _ _) _ -> return cxt
                _ -> error $ "superPredicates called on "
                    ++show predClass
                    ++", which is not a class of kind `Type -> Constraint`"
            newCxt <- mapM superPredicates (filter (`notElem` prevCxt) $ map (subPred predType) cxt)
            return $ nub $ pred:prevCxt++concat newCxt
--         go prevCxt pred = return $ nub $ pred:prevCxt

        -- This helper function is what keeps track of the tags we've used so far
        subPred :: Pred -> Pred -> Pred
        subPred predType' (AppT (ConT predClass) predType) = AppT (ConT predClass) $ go predType
            where
                go (AppT t1 t2) = AppT t1 $ go t2
                go (VarT t) = predType'
                go t = t
--         subPred _ t = t
