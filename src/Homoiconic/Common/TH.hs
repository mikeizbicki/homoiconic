{-# LANGUAGE TupleSections #-}

module Homoiconic.Common.TH
    where

import Prelude
import Control.Monad
import Data.List
import Data.Foldable
import Data.Typeable

import Data.Kind
import GHC.Exts hiding (IsList(..))

import Language.Haskell.TH hiding (Type)
import qualified Language.Haskell.TH as TH

import Debug.Trace

--------------------------------------------------------------------------------

renameClassMethod :: Name -> String
renameClassMethod n = concatMap go $ nameBase n
    where
        go '+' = "plus"
        go '-' = "minus"
        go '.' = "dot"
        go '*' = "mul"
        go '/' = "div"
        go '=' = "eq"
        go '>' = "gt"
        go '<' = "lt"
        go x   = [x]

isOperator :: String -> Bool
isOperator str = not $ length str == length (renameClassMethod $ mkName $ str)

isVarT :: TH.Type -> Bool
isVarT (VarT _) = True
isVarT _        = False

-- FIXME:
-- This really needs to be in the Q monad to properly handle the AppT case.
-- Right now, it returns incorrect results for any concrete type constructor being applied to anything.
isConcrete :: TH.Type -> Bool
isConcrete t = go t
    where
        go (VarT _) = False
        go (ConT _) = True
        go (ListT) = True
        go (AppT ListT _) = True
        go (AppT a1 a2) = go a1 && go a2
        go _ = error ("go: t="++show t)

isList :: TH.Type -> Bool
isList ListT = True
isList (AppT t _) = isList t
isList _ = False

-- | Given a type that stores a function:
-- return a list of the arguments to that function,
-- and discard the return value.
getArgs :: TH.Type -> [TH.Type]
getArgs (ForallT _ _ t) = getArgs t
getArgs (AppT (AppT ArrowT t1) t2) = t1:getArgs t2
getArgs t = []

genericArgs :: TH.Type -> [Name]
genericArgs (ForallT _ _ t) = genericArgs t
genericArgs t = map (\i -> mkName $ "a"++show (i-1)) [1 .. length $ getArgs t]

-- | Given a type that stores a function:
-- return the return type of the function
getReturnType :: TH.Type -> TH.Type
getReturnType (ForallT _ _ t) = getReturnType t
getReturnType (AppT (AppT ArrowT _) t2) = getReturnType t2
getReturnType t = t

-- | Given a type with a single bound variable,
-- substitute all occurances of that variable with a different variable.
subForall :: Name -> TH.Type -> TH.Type
subForall n (ForallT [v] _ t) = go t
    where
        go (AppT t1 t2) = AppT (go t1) (go t2)
        go (VarT _) = VarT n
        go t = t

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
        _ -> error $ "listParentClasses called on "++show algName++", which is not a class"
    ret <- forM cxt $ \pred -> case pred of
        (AppT (ConT c) (VarT v)) -> do
            return $ [c]
        _  -> error $ "listParentClasses, super class is too complicated: "++show pred
    return $ nub $ concat ret

