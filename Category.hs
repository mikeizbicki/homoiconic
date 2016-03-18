{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveGeneric #-}

module Category
    where

import qualified Prelude as P
import LocalPrelude hiding ((.))
import Lattice
-- import Tests
import Topology1

-- class Lawful (cxt :: * -> Constraint) (law::Symbol) where
class Lawful2 (cxt :: (k -> k -> Type) -> Constraint) (law::Symbol) where
    type LawDomain cxt law (a::k->k->Type) (b::k) :: Type
    type LawRange  cxt law (a::k->k->Type) (b::k) :: Type
    type LawCxt    cxt law (a::k->k->Type) (b::k) :: Constraint
    law :: LawCxt cxt law a b
        => Proxy cxt
        -> Proxy law
        -> Proxy a
        -> Proxy b
        -> LawDomain cxt law a b
        -> LawRange  cxt law a b
--     law _ _ _ _ = lowerBound

-- class Lawful (cxt :: Constraint) (law::Symbol) where
--     type LawDomain' cxt law :: Type
--     type LawRange'  cxt law :: Type
--     law':: cxt
--         => Proxy cxt
--         -> Proxy law
--         -> LawDomain' cxt law
--         -> LawRange'  cxt law

--------------------------------------------------------------------------------

class Category (cat :: k -> k -> Type) where
    type ValidObject cat (a::k) :: Constraint
    type ValidObject cat (a::k) = ()

    id :: ValidObject cat a => cat a a
    (.) :: cat b c -> cat a b -> cat a c

-- instance Category cat => Lawful (Category cat) "id" where
--     law' _ _ = id.id == id

instance Lawful2 Category "id" where
    type LawDomain Category "id" a b = () -- a b b
    type LawRange  Category "id" a b = Logic (a b b)
    type LawCxt    Category "id" a b = (Topology (a b b), ValidObject a b, Category a)
    law _ _ (Proxy::Proxy a) (Proxy::Proxy (b::k)) () = id.id == (id::a b b)

instance Lawful2 Category "." where
    type LawDomain Category "." a b = (a b b, a b b, a b b)
    type LawRange  Category "." a b = Logic (a b b)
    type LawCxt    Category "." a b = (Topology (a b b), Category a)
    law _ _ (Proxy::Proxy (a::k->k->Type)) (Proxy::Proxy (b::k)) (f1,f2,f3::a b b)
        = (f1.f2).f3 == f1.(f2.f3)

----------------------------------------

class Category cat => Functor cat (f::Type->Type) where
    -- FIXME:
    -- the real type signature should be
    -- fmap :: cat a b -> cat (f a) (f b)
    -- but instances with this signature are *super* difficult to make
    fmap :: cat a b -> f a -> f b

instance Functor Hask (Hask a) where
    fmap = P.fmap

--------------------------------------------------------------------------------

type Hask = (->)

instance Category Hask where
    id = P.id
    (.) = (P..)

----------------------------------------

type CxtHask = CxtT Hask
type TopHask = CxtT Hask Topology
type PosHask = CxtT Hask Poset
type LatHask = CxtT Hask Lattice

data CxtT (cat :: k -> k -> Type) cxt (a::k) (b::k) where
    CxtT :: (cxt a, cxt b) => cat a b -> CxtT cat cxt a b

instance Category cat => Category (CxtT cat cxt) where
    type ValidObject (CxtT cat cxt) a = (cxt a, ValidObject cat a)
    id = CxtT id
    (CxtT f1).(CxtT f2) = CxtT $ f1.f2

instance (Functor cat (cat a), Category cat) => Functor (CxtT cat cxt) (CxtT cat cxt a) where
    fmap (CxtT f) (CxtT g) = CxtT (fmap f g)

proveCxtT :: (cxt a, cxt b) => cat a b -> CxtT cat cxt a b
proveCxtT = CxtT
