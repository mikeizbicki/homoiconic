{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

module Homogeneous.FAlgebra
    (

    -- * FAlgebra
      FAlgebra (..)
    , Free (..)
    , AST
    , runAST
    , View (..)

    -- ** Template Haskell
    , mkFAlgebra

    -- * Variety
    , Variety (..)
    , Law (..)
    , allLaws
    , subVars

    -- ** Common laws
    , Op0
    , Op1
    , Op2
    , commutative
    , associative
    , idempotent
    , identity_left
    , identity_right

    -- ** Variables for generating laws
    , Var
    , mkExprVar
    , var1
    , var2
    , var3

    -- ** Printing laws
    , printAllLaws
    , printLaws
    , printLaw

    -- ** Evaluating laws
    , Testable

    -- *** Exact
    , runTests
    , runAllTests

    , law2property
    , class2quickcheck

    , law2tasty
    , class2tasty
    , superclasses2tasty

    -- *** Approximate
    , isNeighbor
    , Approximate (..)
    )
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
-- import qualified Test.Tasty.SmallCheck as SC
import qualified Test.Tasty.QuickCheck as QC
import Test.QuickCheck hiding (Testable)

import TemplateHaskellUtils
import Language.Haskell.TH hiding (Type)
import qualified Language.Haskell.TH as TH

import Debug.Trace

--------------------------------------------------------------------------------

class (alg1 a, alg2 a) => And (alg1 :: Type -> Constraint) (alg2 :: Type -> Constraint) (a:: Type)
instance (alg1 a, alg2 a) => And alg1 alg2 a

instance (FAlgebra alg1, FAlgebra alg2) => FAlgebra (And alg1 alg2) where
    type ParentClasses (And alg1 alg2) = ParentClasses alg1++ParentClasses alg2
    data Sig (And alg1 alg2) a where
        Sig_And_alg1 :: Sig alg1 a -> Sig (And alg1 alg2) a
        Sig_And_alg2 :: Sig alg2 a -> Sig (And alg1 alg2) a
    runSig (Sig_And_alg1 s) = runSig s
    runSig (Sig_And_alg2 s) = runSig s

instance (Functor (Sig alg1), Functor (Sig alg2)) => Functor (Sig (And alg1 alg2)) where
    fmap f (Sig_And_alg1 s) = Sig_And_alg1 (fmap f s)
    fmap f (Sig_And_alg2 s) = Sig_And_alg2 (fmap f s)

instance (Foldable (Sig alg1), Foldable (Sig alg2)) => Foldable (Sig (And alg1 alg2)) where
    foldr f b (Sig_And_alg1 s) = foldr f b s
    foldr f b (Sig_And_alg2 s) = foldr f b s

instance
    ( Variety alg1
    , Variety alg2
    , ListLaws (And alg1 alg2) (AncestorClasses (And alg1 alg2))
    ) => Variety (And alg1 alg2) where
    laws=[]

-- NOTE:
-- We can't actually make expressions that use both alg1 and alg2 because of this class instance.
-- We need overlapping instances based on differing class constraints,
-- which isn't implemented in GHC.
instance (FAlgebra alg2, View alg' alg1) => View alg' (And alg1 alg2) where
    embedSig = Sig_And_alg1 . embedSig
    unsafeExtractSig (Sig_And_alg1 s) = unsafeExtractSig s

instance
    ( Show (Sig alg1 a)
    , Show (Sig alg2 a)
    ) => Show (Sig (And alg1 alg2) a)
        where
    show (Sig_And_alg1 s) = show s
    show (Sig_And_alg2 s) = show s

--------------------------------------------------------------------------------

class
    ( Functor (Sig alg)
    , Foldable (Sig alg)
    , Typeable alg
    ) => FAlgebra (alg :: Type -> Constraint)
        where
    type ParentClasses alg :: [Type -> Constraint]
    data Sig alg a
    runSig :: alg a => Sig alg a -> a

----------------------------------------

type AncestorClasses alg = Nub (AncestorClasses_ (ParentClasses alg))

type family AncestorClasses_ (xs::[Type -> Constraint]) :: [Type -> Constraint] where
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

data Free (f :: Type -> Type) (a :: Type) where
    Free :: f (Free f a) -> Free f a
    Pure :: a -> Free f a

deriving instance (Eq a, Eq (f (Free f a))) => Eq (Free f a)

instance (Show a, Show (f (Free f a))) => Show (Free f a) where
    show (Pure a) = show a
    show (Free f) = "("++show f++")"

instance Functor f => Functor (Free f) where
    fmap g (Free f) = Free (fmap (fmap g) f)
    fmap g (Pure a) = Pure (g a)

instance (Functor f, Foldable f) => Foldable (Free f) where
    foldMap f (Free fa) = fold $ fmap (foldMap f) fa
    foldMap f (Pure  a) = f a

type AST (alg :: Type -> Constraint) a = Free (Sig alg) a

{-# INLINABLE runAST #-}
runAST :: (FAlgebra alg, alg a) => AST alg a -> a
runAST (Pure a) = a
runAST (Free f) = runSig (fmap runAST f)

class (FAlgebra alg1, FAlgebra alg2) => View alg1 alg2 where
    embedSig         :: Sig alg1 a -> Sig alg2 a
    unsafeExtractSig :: Sig alg2 a -> Sig alg1 a

instance FAlgebra alg => View alg alg where
    embedSig = id
    unsafeExtractSig = id

embedHomAST :: View alg1 alg2 => AST alg1 a -> AST alg2 a
embedHomAST (Free f) = Free $ embedSig $ fmap embedHomAST f
embedHomAST (Pure a) = Pure a

embedLaw :: View alg1 alg2 => Law alg1 -> Law alg2
embedLaw law = law
    { lhs = embedHomAST $ lhs law
    , rhs = embedHomAST $ rhs law
    }

embedLaws :: View alg1 alg2 => [Law alg1] -> [Law alg2]
embedLaws = map embedLaw

----------------------------------------

data Law alg = Law
    { lawName :: String
    , lhs :: AST alg Var
    , rhs :: AST alg Var
    }

deriving instance Show (AST alg Var) => Show (Law alg)

newtype Var = Var String
    deriving (Eq)

instance Show Var where
    show (Var v) = v

mkExprVar :: String -> AST alg Var
mkExprVar str = Pure $ Var str

var1 :: AST alg Var
var1 = Pure $ Var "var1"

var2 :: AST alg Var
var2 = Pure $ Var "var2"

var3 :: AST alg Var
var3 = Pure $ Var "var3"

--------------------

type Op0 alg = AST alg Var
type Op1 alg = AST alg Var -> AST alg Var
type Op2 alg = AST alg Var -> AST alg Var -> AST alg Var

commutative :: Op2 alg -> Law alg
commutative f = Law
    { lawName = "commutative"
    , lhs = f var1 var2
    , rhs = f var2 var1
    }

associative :: Op2 alg -> Law alg
associative f = Law
    { lawName = "associative"
    , lhs = (var1 `f`  var2) `f` var3
    , rhs =  var1 `f` (var2  `f` var3)
    }

idempotent :: Op2 alg -> Law alg
idempotent f = Law
    { lawName = "idempotent"
    , lhs = f var1 var1
    , rhs = var1
    }

identity_left :: Op0 alg -> Op2 alg -> Law alg
identity_left f0 f2 = Law
    { lawName = "identity_left"
    , lhs = f2 f0 var1
    , rhs = var1
    }

identity_right :: Op0 alg -> Op2 alg -> Law alg
identity_right f0 f2 = Law
    { lawName = "identity_right"
    , lhs = f2 var1 f0
    , rhs = var1
    }

--------------------

class (FAlgebra alg, ListLaws alg (AncestorClasses alg)) => Variety alg where
    laws :: [Law alg]

class Variety alg => ListLaws alg (xs::[Type -> Constraint]) where
    listLaws :: Proxy xs -> [(TypeRep,[Law alg])]

instance Variety alg => ListLaws alg '[] where
    listLaws _ = []

instance
    ( Variety alg
    , Variety x
    , View x alg
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
    ( Variety alg
    , Show (AST alg Var)
    ) => IO ()
printAllLaws = do
    forM (allLaws @alg) $ \(t,laws) -> do
        putStrLn $ show t
        forM laws $ \law -> do
            printLaw law

    putStrLn $ show $ typeRep (Proxy::Proxy alg)
    printLaws (Proxy::Proxy alg)
    putStrLn ""

printLaws :: forall alg.
    ( Variety alg
    , Show (AST alg Var)
    ) => Proxy alg -> IO ()
printLaws palg = do
    forM_ (laws::[Law alg]) printLaw

printLaw :: Show (AST alg Var) => Law alg -> IO ()
printLaw law = do
    putStrLn $ "  "++lawName law++":"
    putStrLn $ "    lhs: "++show (lhs law)
    putStrLn $ "    rhs: "++show (rhs law)

----------------------------------------

type Testable a = (Eq a, Arbitrary a, Typeable a)

subVars :: FAlgebra alg => AST alg Var -> [(Var,a)] -> AST alg a
subVars expr varmap = fmap go expr
    where
        go var = case lookup var varmap of
            Just a -> a

law2property :: forall (a :: Type) alg.
    ( FAlgebra alg
    , alg a
    , Eq a
    , Arbitrary a
    ) => Proxy a -> Law alg -> Gen Bool
law2property p law = do
    as <- infiniteListOf (arbitrary::Gen a)
    let varmap = zip (toList (lhs law) ++ toList (rhs law)) as
    return $ (runAST $ subVars (lhs law) varmap)
          == (runAST $ subVars (rhs law) varmap)

class2quickcheck :: forall a alg.
    ( Variety alg
    , alg a
    , Eq a
    , Arbitrary a
    ) => Proxy a -> Proxy alg -> IO ()
class2quickcheck pa _ = forM_ (laws::[Law alg]) $ \law -> do
    putStr $ lawName law++": "
    quickCheck $ law2property pa law

law2tasty :: forall (a :: Type) alg.
    ( FAlgebra alg
    , alg a
    , Testable a
    ) => Proxy a -> Law alg -> TestTree
law2tasty p law = QC.testProperty (lawName law) $ law2property p law

class2tasty :: forall alg a.
    ( Variety alg
    , alg a
    , Testable a
    ) => Proxy alg -> Proxy a -> TestTree
class2tasty palg pa = testGroup
    ( show (typeRep palg) ++ " on " ++ show (typeRep pa) )
    $ map (law2tasty pa) (laws::[Law alg])

superclasses2tasty :: forall alg a.
    ( Variety alg
    , alg a
    , Testable a
    ) => Proxy alg -> Proxy a -> TestTree
superclasses2tasty palg pa = testGroup
    ( show (typeRep palg) ++ " (and superclasses) on " ++ show (typeRep pa) )
    $
    [ testGroup (show t) $ map (law2tasty pa) (laws::[Law alg])
    | (t,laws) <- allLaws @alg
    ]
    ++
    [ class2tasty palg pa
    ]

runTests :: forall alg a.
    ( Variety alg
    , alg a
    , Testable a
    ) => IO ()
runTests = runTasty (class2tasty (Proxy::Proxy alg) (Proxy::Proxy a))

runAllTests :: forall alg a.
    ( Variety alg
    , alg a
    , Testable a
    ) => IO ()
runAllTests = runTasty (superclasses2tasty (Proxy::Proxy alg) (Proxy::Proxy a))

runTasty :: TestTree -> IO ()
runTasty tt = do
    case tryIngredients [consoleTestReporter] (singleOption (HideSuccesses True)) tt of
        Just x -> x
    return ()

--------------------------------------------------------------------------------

isNeighbor :: (Num a, Ord a) => a -> a -> a -> Bool
isNeighbor a1 a2 n = abs (a1-a2) <= n

class (alg a, Variety alg) => Approximate alg a where
    lawError :: Law alg -> [a] -> a

instance {-#OVERLAPPABLE#-} (alg a, Variety alg) => Approximate alg a

--------------------------------------------------------------------------------
-- template haskell functions

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
                        [ ( Bang SourceUnpack SourceStrict
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
    let instEqSig = StandaloneDerivD
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

    -- return the instances
    return $ [instFAlgebra,instEqSig,instFunctor,instFoldable,instShow,instHomFree] ++ instHomViews ++ patSyns

--------------------------------------------------------------------------------
-- utility functions

