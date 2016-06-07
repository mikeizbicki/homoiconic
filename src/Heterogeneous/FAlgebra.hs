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

data HaskTag {-cxt-} a b where
    HaskTag ::
        ( forall (s::[AT]). () --cxt s
            => Proxy s
--             -> Proxy cxt
            -> Proxy a
            -> Proxy b
            -> App s a
            -> App s b
        ) -> HaskTag a b

apHaskTag :: forall t a b . Proxy (t::[AT]) -> HaskTag a b -> App t a -> App t b
apHaskTag pt (HaskTag f) = f pt (Proxy::Proxy a) (Proxy::Proxy b)

class FunctorTag (f::[AT]->Type->Type) where
    fmapTag :: HaskTag a b -> f t a -> f t b

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

class NoCxt (a::k)
instance NoCxt a

haskEval :: forall cxt alg t a.
    ( alg a
    , FAlgebra alg
    , FunctorTag (Sig alg)
    ) => HaskTag (Free (Sig alg) t a) (App t a)
haskEval = HaskTag go
    where
        go :: forall (s::[AT]) .
            ( alg a
            , FAlgebra alg
            , FunctorTag (Sig alg)
            ) => Proxy s
--               -> Proxy cxt
              -> Proxy (Free (Sig alg) t a)
              -> Proxy (App t a)
              -> App s (Free (Sig alg) t a)
              -> App s (App t a)
        go _ _ _ expr = case appFree @s @t @a @alg expr of
            (Pure a) -> appApp
                (Proxy::Proxy s)
                (Proxy::Proxy t)
                (Proxy::Proxy a)
                 a
            (Free f) -> appApp
                    (Proxy::Proxy s)
                    (Proxy::Proxy t)
                    (Proxy::Proxy a)
                $ runSig (Proxy::Proxy a)
                $ fmapTag haskEval f
            (FreeTag f) -> appApp
                    (Proxy::Proxy s)
                    (Proxy::Proxy t)
                    (Proxy::Proxy a)
                $ runSigTag (Proxy::Proxy a)
                $ fmapTag haskEval f

class
    ( View alg1 (s++t) alg2 (s++t)
    ) => ValidView
        (alg1::Type->Constraint)
        (alg2::Type->Constraint)
        (t::[AT])
        (s::[AT])
instance
    ( View alg1 (s++t) alg2 (s++t)
    ) => ValidView alg1 alg2 t s

embedExpr :: forall alg1 alg2 cxt (s::[AT]) t a.
    ( FAlgebra alg1
--     , FunctorTag (ValidView alg1 alg2 t) (Sig alg1)
    , FunctorTag (Sig alg1)
    , ValidView alg1 alg2 t s
    ) => HaskTag
--         (ValidView alg1 alg2 t)
        (Free (Sig alg1) t a)
        (Free (Sig alg2) t a)
embedExpr = HaskTag go
    where
        go :: forall (s::[AT]).
            ( FAlgebra alg1
            , FunctorTag (Sig alg1)
--             , FunctorTag (ValidView alg1 alg2 t) (Sig alg1)
            , ValidView alg1 alg2 t s
            ) => Proxy s
--               -> Proxy (ValidView alg1 alg2 t)
              -> Proxy (Free (Sig alg1) t a)
              -> Proxy (Free (Sig alg2) t a)
              -> App s (Free (Sig alg1) t a)
              -> App s (Free (Sig alg2) t a)
        go _ _ _ expr = case appFree @s @t @a @alg1 expr of
            (Pure a) -> appFree' @s @t @a @alg2 (Pure a)
            (Free f) -> appFree' @s @t @a @alg2
                $ Free
                $ embedSig
--                 $ _ embedExpr f
                $ fmapTag  embedExpr f
-- --             (FreeTag f) -> appFree' @s @t @a @alg2
-- --                 $ FreeTag
-- --                 $ embedSig
-- --                 $ fmapTag @(ValidView alg1 alg2 t) embedExpr f

appFree :: forall (s::[AT]) t a alg. App s (Free (Sig alg) t a) -> Free (Sig alg) (s++t) a
appFree = unsafeCoerce

appFree' :: forall (s::[AT]) t a alg. Free (Sig alg) (s++t) a -> App s (Free (Sig alg) t a)
appFree' = unsafeCoerce

appApp :: Proxy (s::[AT]) -> Proxy t -> Proxy a -> App (s++t) a -> App s (App t a)
appApp _ _ _ = unsafeCoerce

----------------------------------------

class Typeable alg => FAlgebra (alg::Type->Constraint) where
    data Sig alg (t::[AT]) a

    runSigTag :: alg a => proxy a -> Sig alg (s ':  t) (App t a) -> App (s ':  t) a
    runSig    :: alg a => proxy a -> Sig alg        t  (App t a) -> App        t  a

    mape :: (TypeConstraints t' a)
         => (forall s. Free (Sig alg') s a -> App s a)
         -> Sig alg t (Free (Sig alg') t' a)
         -> Sig alg t (App t' a)

----------------------------------------

class (FAlgebra alg1, FAlgebra alg2) => View alg1 t1 alg2 t2 where
    embedSig          :: Sig alg1       t1  a -> Sig alg2       t2  a
    unsafeExtractSig  :: Sig alg2       t2  a -> Sig alg1       t1  a

--     embedExpr         :: Free (Sig alg1) t1 a -> Free (Sig alg2) t2 a
--     unsafeExtractExpr :: Free (Sig alg2) t2 a -> Free (Sig alg1) t1 a

embedSigTag :: View alg1 (t ': t1) alg2 (t ': t2) => Sig alg1 (t ': t1) a -> Sig alg2 (t ': t2) a
embedSigTag = embedSig

instance FAlgebra alg => View alg t alg t where
    embedSig = id
    unsafeExtractSig = id

--------------------------------------------------------------------------------

type Expr (alg::Type->Constraint) t a = Free (Sig alg) t a

data Law alg t = Law
    { lawName :: String
    , lhs :: Expr alg t Var
    , rhs :: Expr alg t Var
    }

deriving instance Show (Expr alg t Var) => Show (Law alg t)

newtype Var = Var String
    deriving (Eq)

instance Show Var where
    show (Var v) = v

var1 :: Expr alg '[] Var
var1 = Pure $ Var "var1"

var2 :: Expr alg '[] Var
var2 = Pure $ Var "var2"

var3 :: Expr alg '[] Var
var3 = Pure $ Var "var3"

--------------------

-- type Op0 alg = Expr alg Var
-- type Op1 alg = Expr alg Var -> Expr alg Var
-- type Op2 alg = Expr alg Var -> Expr alg Var -> Expr alg Var
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

type ClassSig = (Type->Constraint,[AT])

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
--     { lhs = embedExpr $ lhs law
--     , rhs = embedExpr $ rhs law
--     }
--
-- embedLaws :: View alg1 t1 alg2 t2 => [Law alg1 t1] -> [Law alg2 t2]
-- embedLaws = map embedLaw

--------------------------------------------------------------------------------

-- printAllLaws :: forall alg.
--     ( Variety alg
--     , Show (Expr alg Var)
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
    , Show (Expr alg '[] Var)
    ) => Proxy alg -> IO ()
printLaws palg = do
    forM_ (laws::[Law alg '[]]) printLaw

printLaw :: Show (Expr alg t Var) => Law alg t -> IO ()
printLaw law = do
    putStrLn $ "  "++lawName law++":"
    putStrLn $ "    lhs: "++show (lhs law)
    putStrLn $ "    rhs: "++show (rhs law)

----------------------------------------

type Testable a = (Eq a, Arbitrary a, Typeable a)

-- subVars :: (Functor (Sig alg t), FAlgebra alg) => Expr alg t Var -> [(Var,a)] -> Expr alg t a
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
--     return $ (eval $ subVars (lhs law) varmap)
--           == (eval $ subVars (rhs law) varmap)

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
