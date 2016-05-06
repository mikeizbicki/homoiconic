{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module FAlgebra98
    (

    -- * FAlgebra
      FAlgebra98 (..)
    , Free98 (..)
    , Expr98
    , eval98
    , View98 (..)

    -- ** Template Haskell
    , mkFAlgebra98

    -- * Variety
    , Variety98 (..)
    , Law (..)
    , var1
    , var2
    , var3

    , printAllLaws
    , printLaws

    )
    where

import Prelude
import Control.Monad
import Data.List
import Data.Typeable
import GHC.Exts

import Language.Haskell.TH

import Debug.Trace

--------------------------------------------------------------------------------

type family MapCxt (f :: (* -> Constraint) -> Constraint) (xs :: [* -> Constraint]) :: Constraint where
    MapCxt f '[] = ()
    MapCxt f (x ': xs) = (f x, MapCxt f xs)

class
    ( MapCxt FAlgebra98 (ParentClasses alg)
    , Functor (Sig98 alg)
    , Typeable alg
    , MapProxy (ParentClasses alg)
    , Show (Expr98 alg Var)
    ) => FAlgebra98 (alg :: * -> Constraint)
        where
    type ParentClasses alg :: [* -> Constraint]
    data Sig98 alg a
    runSig98 :: alg a => Sig98 alg a -> a

data Free98 (f :: * -> *) (a :: *) where
    Free98 :: f (Free98 f a) -> Free98 f a
    Pure98 :: a -> Free98 f a

instance (Show a, Show (f (Free98 f a))) => Show (Free98 f a) where
    show (Pure98 a) = show a
    show (Free98 f) = "("++show f++")"

type Expr98 (alg :: * -> Constraint) a = Free98 (Sig98 alg) a

eval98 :: (FAlgebra98 alg, alg a) => Expr98 alg a -> a
eval98 (Pure98 a) = a
eval98 (Free98 f) = runSig98 (Prelude.fmap eval98 f)

class (FAlgebra98 alg1, FAlgebra98 alg2) => View98 alg1 alg2 where
    embedSig         :: Sig98 alg1 a -> Sig98 alg2 a
    unsafeExtractSig :: Sig98 alg2 a -> Sig98 alg1 a

instance FAlgebra98 alg => View98 alg alg where
    embedSig = id
    unsafeExtractSig = id

----------------------------------------

data Law alg = Law
    { name :: String
    , lhs :: Expr98 alg Var
    , rhs :: Expr98 alg Var
    }

deriving instance Show (Expr98 alg Var) => Show (Law alg)

newtype Var = Var String

instance Show Var where
    show (Var v) = v

var1 :: Expr98 alg Var
var1 = Pure98 $ Var "var1"

var2 :: Expr98 alg Var
var2 = Pure98 $ Var "var2"

var3 :: Expr98 alg Var
var3 = Pure98 $ Var "var3"

class
    ( FAlgebra98 alg
    , MapCxt FAlgebra98 (ParentClasses alg)
    ) => Variety98 alg
        where
    laws :: [Law alg]

printAllLaws :: forall alg.
    ( Variety98 alg
    ) => Proxy alg -> IO ()
printAllLaws p = do
    mapProxy printAllLaws (Proxy::Proxy (ParentClasses alg))
    putStrLn $ show (typeRep p) ++ " laws:"
    printLaws @alg
    putStrLn ""

class MapProxy (xs::[* -> Constraint]) where
    mapProxy :: (forall x. Variety98 x => Proxy (x:: * -> Constraint) -> IO ()) -> Proxy xs -> IO ()

instance MapProxy '[] where
    mapProxy f _ = return ()

instance (Variety98 x, MapProxy xs) => MapProxy ((x:: * -> Constraint) ': xs) where
    mapProxy f p = do
        f (Proxy::Proxy x)
        mapProxy f (Proxy::Proxy xs)

printLaws :: forall alg.
    ( Variety98 alg
    , Show (Expr98 alg Var)
    ) => IO ()
printLaws = do
    forM_ (laws::[Law alg]) printLaw

printLaw :: Show (Expr98 alg Var) => Law alg -> IO ()
printLaw law = do
    putStrLn $ "  "++name law++":"
    putStrLn $ "    lhs: "++show (lhs law)
    putStrLn $ "    rhs: "++show (rhs law)

--------------------------------------------------------------------------------
-- template haskell functions

-- | Constructs instances for the FAlgebra98 and related classes.
mkFAlgebra98 :: Name -> Q [Dec]
mkFAlgebra98 algName = do

    -- validate input and extract the class functions
    qinfo <- reify algName
    decs <- case qinfo of
        ClassI (ClassD cxt _ [_] _ decs) _ -> return decs
        _ -> error $ "mkFAlgebra called on "
            ++show algName
            ++", which is not a class of kind `Type -> Constraint`"

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
                ( ConT $ mkName "FAlgebra98" )
                ( ConT $ algName)
            )
            [ DataInstD
                []
                ( mkName "Sig98" )
                [ ConT algName, VarT varName ]
                Nothing
                (
                    -- create a constructor for each parent class to hold their signatures
                    [ NormalC
                        ( mkName $ "Sig98_"++nameBase algName++"_"++nameBase parentClass)
                        [ ( Bang SourceUnpack SourceStrict
                          , AppT
                            ( AppT
                                ( ConT $ mkName "Sig98" )
                                ( ConT parentClass )
                            )
                            ( VarT varName )
                          )
                        ]
                        | parentClass <- parentClasses
                    ]
                    ++

                    -- create a constructor for each member function
                    [ NormalC
                        ( mkName $ "Sig98_" ++ renameClassMethod sigName )
                        ( map (Bang NoSourceUnpackedness NoSourceStrictness,) (getArgs $ subForall varName sigType) )
                        | SigD sigName sigType <- decs
                    ]
                )
                []

            , FunD
                ( mkName "runSig98" )
                [ let args = args2pat sigName $ getArgs $ subForall (mkName "e") sigType
                  in Clause
                    [ ConP ( mkName $ "Sig98_" ++ renameClassMethod sigName ) args
                    ]
                    ( NormalB $ foldl AppE (VarE sigName) $ map (\(VarP n)->VarE n) args )
                    []
                    | SigD sigName sigType <- decs
                ]

            , TySynInstD
                ( mkName $ "ParentClasses" )
                ( TySynEqn
                    [ ConT $ algName ]
                    ( foldl (\b a -> AppT (AppT PromotedConsT (ConT a)) b) PromotedNilT parentClasses )
                )
            ]

    -- construct the Functor (Sig alg) instance
    let instFunctor = InstanceD
            Nothing
            []
            ( AppT
                ( ConT $ mkName "Functor")
                ( AppT
                    ( ConT $ mkName "Sig98" )
                    ( ConT $ algName )
                )
            )
            [ FunD
                ( mkName "fmap" )
                [ let args = args2pat sigName $ getArgs $ subForall (mkName "e") sigType
                  in Clause
                    [ VarP $ mkName "f"
                    , ConP ( mkName $ "Sig98_" ++ renameClassMethod sigName ) args
                    ]
                    ( NormalB $ foldl AppE (ConE (mkName $ "Sig98_" ++ renameClassMethod sigName))
                        [ AppE
                            ( VarE $ mkName "f" )
                            ( VarE $ n )
                        | VarP n <- args
                        ]
                    )
                    []
                    | SigD sigName sigType <- decs
                ]
            ]

    -- construct the `Show a => Show (Sig98 alg a)` instance
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
                        ( ConT $ mkName "Sig98" )
                        ( ConT algName )
                    )
                    ( VarT $ varName )
                )
            )
            [ FunD
                ( mkName "show" )
                (
                    [ Clause
                        [ ConP
                            ( mkName $ "Sig98_"++nameBase algName++"_"++nameBase parentClass)
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
                    [ let args = args2pat sigName $ getArgs $ subForall (mkName "e") sigType
                      in Clause
                        [ ConP
                            ( mkName $ "Sig98_" ++ renameClassMethod sigName )
                            args
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
                                                ( VarE $ mkName "e0" )
                                            )
                                        )
                                        ( LitE $ StringL $ nameBase sigName )
                                    )
                                )
                                ( AppE
                                    ( VarE $ mkName "show" )
                                    ( VarE $ mkName "e1" )
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
                                ( map (\(VarP n)->VarE n) args )
                        )
                        []
                        | SigD sigName sigType <- decs
                    ]
                )
            ]

    -- construct the `View98 alg alg' => alg (Free98 (Sig98 alg') a)` instance
    let algName' = mkName "alg'"
    let instFree98 = InstanceD
            Nothing
            [ AppT
                ( AppT
                    ( ConT $ mkName "View98" )
                    ( ConT n )
                )
                ( VarT algName' )
            | n <- algName:superClasses
            ]
            ( AppT
                ( ConT algName )
                ( AppT
                    ( AppT
                        ( ConT $ mkName "Free98" )
                        ( AppT
                            ( ConT $ mkName "Sig98" )
                            ( VarT algName' )
                        )
                    )
                    ( VarT varName )
                )
            )
            [ let args = args2pat sigName $ getArgs $ subForall (mkName "e") sigType
              in FunD
                sigName
                [ Clause
                    args
                    ( NormalB $ AppE
                        ( ConE $ mkName "Free98" )
                        ( AppE
                            ( VarE $ mkName "embedSig" )
                            ( foldl AppE (ConE $ mkName $ "Sig98_"++renameClassMethod sigName)
                                $ map (\(VarP n)->VarE n) args
                            )
                        )
                    )
                    []
                ]
            | SigD sigName sigType <- decs
            ]

    -- construct the `View98 alg alg'` instances
    let instView98s =

            -- parent classes are stored directly in the Sig98 type
            [ InstanceD
                Nothing
                []
                ( AppT
                    ( AppT
                        ( ConT $ mkName "View98" )
                        ( ConT superClass )
                    )
                    ( ConT algName )
                )
                [ FunD
                    ( mkName "embedSig" )
                    [ Clause
                        []
                        ( NormalB $ ConE $ mkName $ "Sig98_"++nameBase algName++"_"++nameBase superClass )
                        []
                    ]
                , FunD
                    ( mkName "unsafeExtractSig" )
                    [ Clause
                        [ ConP
                            ( mkName $ "Sig98_"++nameBase algName++"_"++nameBase superClass )
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
                        ( ConT $ mkName "View98" )
                        ( ConT superClass )
                    )
                    ( ConT algName )
                )
                [ FunD
                    ( mkName "embedSig" )
                    [ Clause
                        [ VarP $ mkName "s" ]
                        ( NormalB $ AppE
                            ( ConE $ mkName $ "Sig98_"++nameBase algName++"_"++nameBase parentClass )
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
                            ( mkName $ "Sig98_"++nameBase algName++"_"++nameBase parentClass )
                            [ VarP $ mkName "s" ]
                        ]
                        ( NormalB $ AppE
                            ( VarE $ mkName "unsafeExtractSig" )
                            ( VarE $ mkName "s" )
                        )
                        []
                    ]
                ]
--                 []
            | (parentClass,superClass) <- superClassesWithParents
            ]

    -- return the instances
    return $ [instFAlgebra,instFunctor,instShow,instFree98] ++ instView98s

--------------------------------------------------------------------------------
-- utility functions

renameClassMethod :: Name -> String
renameClassMethod n = concatMap go $ nameBase n
    where
        go '+' = "plus"
        go '-' = "minus"
        go '.' = "dot"
        go '*' = "mul"
        go x   = [x]

isOperator :: String -> Bool
isOperator str = not $ length str == length (renameClassMethod $ mkName $ str)

-- | Given a type that stores a function:
-- return a list of the arguments to that function,
-- and discard the return value.
getArgs :: Type -> [Type]
getArgs (AppT (AppT ArrowT t1) t2) = t1:getArgs t2
getArgs t = []

-- | Given a type with a single bound variable,
-- substitute all occurances of that variable with a different variable.
subForall :: Name -> Type -> Type
subForall n (ForallT [v] _ t) = go t
    where
        go (AppT t1 t2) = AppT (go t1) (go t2)
        go (VarT _) = VarT n
        go t = t

-- | Given a list of arguments passed to a function, return a list of patterns;
-- the inputs must be all type variables, otherwise an error will be thrown;
-- the Name parameter is only used for better error messages;
-- the output patterns will contain variables e1,e2,...eN where N is the length of the input
args2pat :: Name -> [Type] -> [Pat]
args2pat sigName xs = go 0 xs
    where
        go i [] = []
        go i (VarT n:xs) = (VarP $ mkName $ nameBase n ++ show i):go (i+1) xs
        go i (x:xs) = error $ "function "++nameBase sigName++" has unsupported argument type "++show (ppr x)

-- | Given a class name, find all the superclasses
listSuperClasses :: Name -> Q [Name]
listSuperClasses algName = do
    qinfo <- reify algName
    cxt <- case qinfo of
        ClassI (ClassD cxt _ _ _ _) _ -> return cxt
        _ -> error $ "listSuperClasses called on "++show algName++", which is not a class"
    ret <- forM cxt $ \pred -> case pred of
        (AppT (ConT c) (VarT v)) -> do
            ret <- listSuperClasses c
            return $ c:ret
        _  -> error $ "listSuperClasses, super class is too complicated: "++show pred
    return $ nub $ concat ret

-- | Fiven a class name, find all the superclasses that are not also parents;
-- for each superclass, record the parent class that gives rise to the superclass;
-- if there are multiple ways to reach the superclass,
-- then an arbitrary parent will be selected
listSuperClassesWithParents :: Name -> Q [(Name,Name)]
listSuperClassesWithParents algName = do
    parentClasses <- listParentClasses algName
    superClassesWithParents <- fmap concat $ forM parentClasses $ \parentClass -> do
        superClasses <- listSuperClasses parentClass
        return $ map (parentClass,) superClasses
    return $ nubBy (\(_,a1) (_,a2) -> a1==a2) superClassesWithParents

-- | Given a class name, find all the parent classes
listParentClasses :: Name -> Q [Name]
listParentClasses algName = do
    qinfo <- reify algName
    cxt <- case qinfo of
        ClassI (ClassD cxt _ _ _ _) _ -> return cxt
        _ -> error $ "listSuperClasses called on "++show algName++", which is not a class"
    ret <- forM cxt $ \pred -> case pred of
        (AppT (ConT c) (VarT v)) -> do
            return $ [c]
        _  -> error $ "listSuperClasses, super class is too complicated: "++show pred
    return $ nub $ concat ret

