{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoRebindableSyntax #-}

{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

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
    , allLaws

    -- ** Variables for generating laws
    , Var
    , var1
    , var2
    , var3

    -- ** Printing laws
    , printAllLaws
    , printLaws
    , printLaw

    -- ** Evaluating laws
    , Testable98
    , runTests
    , runAllTests

    , class2tasty
    , superclasses2tasty

    )
    where

import Prelude
import Control.Monad
import Data.List
import Data.Foldable
import Data.Typeable
import GHC.Exts hiding (IsList(..))

import Test.Tasty
import Test.Tasty.Ingredients.Basic
import Test.Tasty.Options
import Test.Tasty.Runners
import qualified Test.Tasty.SmallCheck as SC
import qualified Test.Tasty.QuickCheck as QC
import Test.QuickCheck hiding (Testable)

import Language.Haskell.TH

import Debug.Trace

--------------------------------------------------------------------------------

class (alg1 a, alg2 a) => And (alg1 :: * -> Constraint) (alg2 :: * -> Constraint) (a:: *)
instance (alg1 a, alg2 a) => And alg1 alg2 a

instance (FAlgebra98 alg1, FAlgebra98 alg2) => FAlgebra98 (And alg1 alg2) where
    type ParentClasses (And alg1 alg2) = ParentClasses alg1++ParentClasses alg2
    data Sig98 (And alg1 alg2) a where
        Sig98_And_alg1 :: Sig98 alg1 a -> Sig98 (And alg1 alg2) a
        Sig98_And_alg2 :: Sig98 alg2 a -> Sig98 (And alg1 alg2) a
    runSig98 (Sig98_And_alg1 s) = runSig98 s
    runSig98 (Sig98_And_alg2 s) = runSig98 s

instance (Functor (Sig98 alg1), Functor (Sig98 alg2)) => Functor (Sig98 (And alg1 alg2)) where
    fmap f (Sig98_And_alg1 s) = Sig98_And_alg1 (fmap f s)
    fmap f (Sig98_And_alg2 s) = Sig98_And_alg2 (fmap f s)

instance (Foldable (Sig98 alg1), Foldable (Sig98 alg2)) => Foldable (Sig98 (And alg1 alg2)) where
    foldr f b (Sig98_And_alg1 s) = foldr f b s
    foldr f b (Sig98_And_alg2 s) = foldr f b s

instance
    ( Variety98 alg1
    , Variety98 alg2
    , ListLaws (And alg1 alg2) (AncestorClasses (And alg1 alg2))
    ) => Variety98 (And alg1 alg2) where
    laws=[]

-- NOTE:
-- We can't actually make expressions that use both alg1 and alg2 because of this class instance.
-- We need overlapping instances based on differing class constraints,
-- which isn't implemented in GHC.
instance (FAlgebra98 alg2, View98 alg' alg1) => View98 alg' (And alg1 alg2) where
    embedSig = Sig98_And_alg1 . embedSig
    unsafeExtractSig (Sig98_And_alg1 s) = unsafeExtractSig s

instance
    ( Show (Sig98 alg1 a)
    , Show (Sig98 alg2 a)
    ) => Show (Sig98 (And alg1 alg2) a)
        where
    show (Sig98_And_alg1 s) = show s
    show (Sig98_And_alg2 s) = show s

--------------------------------------------------------------------------------

class
    ( Functor (Sig98 alg)
    , Foldable (Sig98 alg)
    , Typeable alg
    ) => FAlgebra98 (alg :: * -> Constraint)
        where
    type ParentClasses alg :: [* -> Constraint]
    data Sig98 alg a
    runSig98 :: alg a => Sig98 alg a -> a

----------------------------------------

type AncestorClasses alg = Nub (AncestorClasses_ (ParentClasses alg))

type family AncestorClasses_ (xs::[* -> Constraint]) :: [* -> Constraint] where
    AncestorClasses_ (x ': xs) = x ': (AncestorClasses_ (ParentClasses x) ++ AncestorClasses_ xs)
    AncestorClasses_ '[] = '[]

type family (++) (xs1:: [x]) (xs2:: [x]) :: [x] where
    '[] ++ '[] = '[]
    '[] ++ xs2 = xs2
    xs1 ++ '[] = xs1
    (x ': xs1) ++ xs2 = x ': (xs1++xs2)

type family Nub xs where
    Nub '[] = '[]
    Nub (x ': xs) = x ': Nub (Remove x xs)

type family Remove x xs where
    Remove x '[]       = '[]
    Remove x (x ': ys) =      Remove x ys
    Remove x (y ': ys) = y ': Remove x ys

----------------------------------------

data Free98 (f :: * -> *) (a :: *) where
    Free98 :: f (Free98 f a) -> Free98 f a
    Pure98 :: a -> Free98 f a

instance (Show a, Show (f (Free98 f a))) => Show (Free98 f a) where
    show (Pure98 a) = show a
    show (Free98 f) = "("++show f++")"

instance Functor f => Functor (Free98 f) where
    fmap g (Free98 f) = Free98 (fmap (fmap g) f)
    fmap g (Pure98 a) = Pure98 (g a)

instance (Functor f, Foldable f) => Foldable (Free98 f) where
    foldMap f (Free98 fa) = fold $ fmap (foldMap f) fa
    foldMap f (Pure98  a) = f a

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

embedExpr98 :: View98 alg1 alg2 => Expr98 alg1 a -> Expr98 alg2 a
embedExpr98 (Free98 f) = Free98 $ embedSig $ fmap embedExpr98 f
embedExpr98 (Pure98 a) = Pure98 a

embedLaw :: View98 alg1 alg2 => Law alg1 -> Law alg2
embedLaw law = law
    { lhs = embedExpr98 $ lhs law
    , rhs = embedExpr98 $ rhs law
    }

embedLaws :: View98 alg1 alg2 => [Law alg1] -> [Law alg2]
embedLaws = map embedLaw

----------------------------------------

data Law alg = Law
    { name :: String
    , lhs :: Expr98 alg Var
    , rhs :: Expr98 alg Var
    }

deriving instance Show (Expr98 alg Var) => Show (Law alg)

newtype Var = Var String
    deriving (Eq)

instance Show Var where
    show (Var v) = v

var1 :: Expr98 alg Var
var1 = Pure98 $ Var "var1"

var2 :: Expr98 alg Var
var2 = Pure98 $ Var "var2"

var3 :: Expr98 alg Var
var3 = Pure98 $ Var "var3"

class (FAlgebra98 alg, ListLaws alg (AncestorClasses alg)) => Variety98 alg where
    laws :: [Law alg]

class Variety98 alg => ListLaws alg (xs::[* -> Constraint]) where
    listLaws :: Proxy xs -> [(TypeRep,[Law alg])]

instance Variety98 alg => ListLaws alg '[] where
    listLaws _ = []

instance
    ( Variety98 alg
    , Variety98 x
    , View98 x alg
    , ListLaws alg xs
    ) => ListLaws alg (x ': xs)
        where
    listLaws _ =
        [ (typeRep (Proxy::Proxy x), embedLaws (laws::[Law x])) ]
        ++ listLaws (Proxy::Proxy xs)

allLaws :: forall alg. ListLaws alg (AncestorClasses alg) => [(TypeRep,[Law alg])]
allLaws = listLaws (Proxy::Proxy (AncestorClasses alg))

--------------------------------------------------------------------------------

printAllLaws :: forall alg.
    ( Variety98 alg
    , Show (Expr98 alg Var)
    ) => IO ()
printAllLaws = do
    forM (allLaws @alg) $ \(t,laws) -> do
        putStrLn $ show t
        forM laws $ \law -> do
            printLaw law
    putStrLn ""

printLaws :: forall alg.
    ( Variety98 alg
    , Show (Expr98 alg Var)
    ) => Proxy alg -> IO ()
printLaws palg = do
    forM_ (laws::[Law alg]) printLaw

printLaw :: Show (Expr98 alg Var) => Law alg -> IO ()
printLaw law = do
    putStrLn $ "  "++name law++":"
    putStrLn $ "    lhs: "++show (lhs law)
    putStrLn $ "    rhs: "++show (rhs law)

----------------------------------------

type Testable98 a = (Eq a, Arbitrary a, Typeable a)

subVars :: FAlgebra98 alg => Expr98 alg Var -> [(Var,a)] -> Expr98 alg a
subVars expr varmap = fmap go expr
    where
        go var = case lookup var varmap of
            Just a -> a

law2quickcheck :: forall (a :: *) alg.
    ( FAlgebra98 alg
    , alg a
    , Testable98 a
    ) => Proxy a -> Law alg -> TestTree
law2quickcheck p law = QC.testProperty (name law) $ do
    as <- infiniteListOf (arbitrary::Gen a)
    let varmap = zip (toList (lhs law) ++ toList (rhs law)) as
    return $ (eval98 $ subVars (lhs law) varmap)
          == (eval98 $ subVars (rhs law) varmap)

class2tasty :: forall alg a.
    ( Variety98 alg
    , alg a
    , Testable98 a
    ) => Proxy alg -> Proxy a -> TestTree
class2tasty palg pa = testGroup
    ( show (typeRep palg) ++ " on " ++ show (typeRep pa) )
    $ map (law2quickcheck pa) (laws::[Law alg])

superclasses2tasty :: forall alg a.
    ( Variety98 alg
    , alg a
    , Testable98 a
    ) => Proxy alg -> Proxy a -> TestTree
superclasses2tasty palg pa = testGroup
    ( show (typeRep palg) ++ " (and superclasses) on " ++ show (typeRep pa) )
    $
    [ testGroup (show t) $ map (law2quickcheck pa) (laws::[Law alg])
    | (t,laws) <- allLaws @alg
    ]
    ++
    [ class2tasty palg pa
    ]

runTests :: forall alg a.
    ( Variety98 alg
    , alg a
    , Testable98 a
    ) => IO ()
runTests = runTasty (class2tasty (Proxy::Proxy alg) (Proxy::Proxy a))

runAllTests :: forall alg a.
    ( Variety98 alg
    , alg a
    , Testable98 a
    ) => IO ()
runAllTests = runTasty (superclasses2tasty (Proxy::Proxy alg) (Proxy::Proxy a))

runTasty :: TestTree -> IO ()
runTasty tt = do
    case tryIngredients [consoleTestReporter] (singleOption (HideSuccesses True)) tt of
        Just x -> x
    return ()


--------------------------------------------------------------------------------
-- template haskell functions

-- | Constructs instances for FAlgebra98 and related classes.
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
                    -- create a constructor for each member function
                    [ NormalC
                        ( mkName $ "Sig98_" ++ renameClassMethod sigName )
                        ( map (Bang NoSourceUnpackedness NoSourceStrictness,) (getArgs $ subForall varName sigType) )
                        | SigD sigName sigType <- decs
                    ]
                    ++
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
                )
                []

            , FunD
                ( mkName "runSig98" )
                (
                    -- evaluate functions
                    [ let args = args2pat sigName $ getArgs $ subForall (mkName "e") sigType
                      in Clause
                        [ ConP ( mkName $ "Sig98_" ++ renameClassMethod sigName ) args
                        ]
                        ( NormalB $ foldl AppE (VarE sigName) $ map (\(VarP n)->VarE n) args )
                        []
                        | SigD sigName sigType <- decs
                    ]
                    ++
                    -- evaluate nested constructors
                    [ Clause
                        [ ConP
                            ( mkName $ "Sig98_"++nameBase algName++"_"++nameBase parentClass )
                            [ VarP $ mkName $ "s" ]
                        ]
                        ( NormalB $ AppE
                            ( VarE $ mkName "runSig98" )
                            ( VarE $ mkName "s" )
                        )
                        []
                        | parentClass <- parentClasses
                    ]
                )

            , TySynInstD
                ( mkName $ "ParentClasses" )
                ( TySynEqn
                    [ ConT $ algName ]
                    ( foldl (\b a -> AppT (AppT PromotedConsT (ConT a)) b) PromotedNilT parentClasses )
                )
            ]

    -- construct the `Functor (Sig98 alg)` instance
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
                (
                    -- map over constructors for member functions
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
                    ++
                    -- map over embedded constructors
                    [ Clause
                        [ VarP $ mkName "f"
                        , ConP
                            ( mkName $ "Sig98_"++nameBase algName++"_"++nameBase parentClass )
                            [ VarP $ mkName "s" ]
                        ]
                        ( NormalB $ AppE
                            ( ConE $ mkName $ "Sig98_"++nameBase algName++"_"++nameBase parentClass )
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
                )
            ]

    -- construct the `Foldable (Sig98 alg)` instance
    let instFoldable = InstanceD
            Nothing
            []
            ( AppT
                ( ConT $ mkName "Foldable" )
                ( AppT
                    ( ConT $ mkName "Sig98" )
                    ( ConT algName )
                )
            )
            [ FunD
                ( mkName "foldr" )
                (
                    -- fold over constructors for member functions
                    [ let args = args2pat sigName $ getArgs $ subForall (mkName "e") sigType
                      in Clause
                        [ VarP $ mkName "f"
                        , VarP $ mkName "b"
                        , ConP ( mkName $ "Sig98_" ++ renameClassMethod sigName ) args
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
                            ( map (\(VarP n) -> VarE n) $ reverse args )
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
                            ( mkName $ "Sig98_"++nameBase algName++"_"++nameBase parentClass )
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
                )
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
            | (parentClass,superClass) <- superClassesWithParents
            ]

    -- return the instances
    return $ [instFAlgebra,instFunctor,instFoldable,instShow,instFree98] ++ instView98s

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

