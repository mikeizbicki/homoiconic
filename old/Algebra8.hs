{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Algebra8
    where

import LocalPrelude
import Prelude (Functor(..), Applicative(..), Monad(..))
import Prelude ((.))
import qualified Prelude as P

import Unsafe.Coerce

import Data.Kind
import GHC.TypeLits

--------------------------------------------------------------------------------

-- type family Logic  a
-- type family Scalar a

class Poset a where
    inf :: a -> a -> a

(&&) :: Poset a => a -> a -> a
(&&) = inf

-- class Topology a where
class Poset (Logic a) => Topology a where
    type family Logic a
    (==) :: a -> a -> Logic a

class Topology a => Semigroup a where
    (+) :: a -> a -> a

-- class (Scalar (Scalar a)~Scalar a, Semigroup a) => Module a where
-- class (Scalar (Scalar a)~Scalar a, Semigroup (Scalar a), Semigroup a) => Module a where
class (Scalar (Scalar a)~Scalar a, Module (Scalar a), Semigroup a) => Module a where
    type family Scalar a
-- class Semigroup a => Module a where
-- class (Semigroup a, Semigroup (Scalar a)) => Module a where
-- class (Semigroup a, Module (Scalar a)) => Module a where
    (.*) :: Scalar a -> a -> a

class Module a => Hilbert a where
    (<>) :: a -> a -> Scalar a


----------------------------------------

-- type instance Logic () = ()
-- type instance Scalar () = ()

instance Poset () where
    inf () () = ()
instance Topology () where
    type Logic () = ()
    (==) () () = ()
instance Semigroup () where
    (+) () () = ()
instance Module () where
    type Scalar () = ()
    (.*) () () = ()
instance Hilbert () where
    (<>) () () = ()

-- type instance Logic Bool = Bool
-- type instance Scalar Bool = ()
instance Poset Bool where
    inf = (P.&&)
instance Topology Bool where
    type Logic Bool = Bool
    (==) = (P.==)

-- type instance Logic Int = Bool
-- type instance Scalar Int = Int
instance Poset Int where
    inf = P.min
instance Topology Int where
    type Logic Int = Bool
    (==) = (P.==)
instance Semigroup Int where (+) = (P.+)
instance Module Int where
    type Scalar Int = Int
    (.*) = (P.*)
instance Hilbert Int where
    (<>) = (P.*)

-- type instance Logic (a,b) = (Logic a, Logic b)
-- type instance Scalar (a,b) = Scalar b
instance (Poset a, Poset b) => Poset (a,b) where
    inf (a1,b1) (a2,b2) = (inf a1 a2, inf b1 b2)
instance (Topology a, Topology b) => Topology (a,b) where
    type Logic (a,b) = (Logic a, Logic b)
    (a1,b1)==(a2,b2) = (a1==a2,b1==b2)
instance (Semigroup a, Semigroup b) => Semigroup (a,b) where
    (a1,b1)+(a2,b2) = (a1+a2,b1+b2)
instance (Module a, Module b, Semigroup (Scalar b), Scalar a~Scalar b) => Module (a,b) where
    type Scalar (a,b) = Scalar b
    s.*(a,b) = (s.*a,s.*b)
instance (Hilbert a, Hilbert b, Semigroup (Scalar b), Scalar a~Scalar b) => Hilbert (a,b) where
    (a1,b1)<>(a2,b2) = (a1<>a2)+(b1<>b2)

--------------------------------------------------------------------------------

type Space = Hilbert

x :: Expr Space (Int,Int)
x = Pure (1,5)

y :: Expr Space (Int,Int)
y = Pure (1,4)

z :: Scalar (Expr Space (Int,Int) )
z = Pure 3

--------------------------------------------------------------------------------

type Expr alg a = Free (Sig alg) '[] a

data Free (f::[AT]->Type->Type) (t::[AT]) (a::Type) where
    FreeTag  :: TypeConstraints t a => f (s ': t) (Free f t a)  -> Free f (s ': t) a
    Free     :: TypeConstraints t a => f       t  (Free f t a)  -> Free f       t  a
    Pure     :: App t a -> Free f t a

--------------------

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

-- NOTE:
-- Earlier versions of GHC can't use the ShowUntag family above,
-- and so they need the overlapping instances implementation below.
-- AFAIK, there is no disadvantage to this version.

-- instance
--     ( Show      (App t a)
--     , Show      (f t (Free f t a))
--     ) => Show (Free f t a)
--         where
--     show (Free        f) = show f
--     show (Pure        a) = show a
--
-- instance {-#OVERLAPS#-}
--     ( Show      (App (Tag s t) a)
--     , Show      (f (Tag s t) (Free f (Tag s t) a))
--     , Show      (f (Tag s t) (Free f (      t) a))
--     ) => Show (Free f (Tag s t) a)
--         where
--     show (FreeTag     f) = show f
--     show (Free        f) = show f
--     show (Pure        a) = show a

----------------------------------------

-- NOTE:
-- There's no need for this class based eval function anymore.
-- I believe (?) this was required when the types families were associated to a class.
--
-- class Eval alg (t::AT) a where
--     go :: Free (Sig alg) t a -> App t a
--
-- instance
--     ( Functor (Sig alg 'Id)
--     , FAlgebra alg
--     , alg a
--     ) => Eval alg 'Id a
--         where
--     go (Free f) = alg (Proxy :: Proxy a)   $ fmap go f
--     go (Pure a) = a
--
-- instance
--     ( FAlgebra alg
--     , Functor (Sig alg (Tag s t))
--     , Eval alg t a
--     , alg a
--     ) => Eval alg (Tag s t) a
--         where
--     go (FreeTag     f) = algTag (Proxy :: Proxy a) $ fmap go f
--     go (Free        f) = alg    (Proxy :: Proxy a) $ fmap go f
--     go (Pure        a) = a

eval :: forall alg t a.
    ( FAlgebra alg
    , alg a
    ) => Free (Sig alg) t a -> App t a
eval (Pure    a) = a
eval (Free    s) = alg    (Proxy::Proxy a) $ mape eval s
eval (FreeTag s) = algTag (Proxy::Proxy a) $ mape eval s

----------------------------------------

-- type instance Logic  (Free (Sig alg) t a) = Free (Sig alg) ('Logic  ': t) a
-- -- type instance Scalar (Free (Sig alg) t a) = Free (Sig alg) ('Scalar ': t) a
-- type instance Scalar (Free (Sig alg) t a) = Free (Sig alg) (AppScalar t) a

type family AppScalar (xs::[AT]) :: [AT] where
    AppScalar ('Scalar ': xs) = 'Scalar ': xs
    AppScalar xs              = 'Scalar ': xs

type TypeConstraints (t::[AT]) (a::Type)
    = ( App (AppScalar t) a ~ Scalar (App t a)
      )

----------------------------------------

class FAlgebra (alg::Type->Constraint) where
    data Sig alg (t::[AT]) a

    algTag :: alg a => proxy a -> Sig alg (s ':  t) (App t a) -> App (s ':  t) a
    alg    :: alg a => proxy a -> Sig alg        t  (App t a) -> App        t  a

    mape :: (TypeConstraints t' a)
         => (forall s. Free (Sig alg') s a -> App s a)
         -> Sig alg t (Free (Sig alg') t' a)
         -> Sig alg t (App t' a)

--------------------

class (Topology a, Variety alg) => Approximate alg a where
    approximation :: Proxy alg -> Proxy a -> String -> Logic a

-- instance {-#OVERLAPPABLE#-} (Topology a, Variety alg) => Approximate alg a where
--     approximation _ _ _ = minBound

--------------------

class FAlgebra alg => Variety alg where
    laws :: [Law alg]

newtype Var = Var String

-- FIXME:
-- We don't want to have to define instance of these classes in order to define the family instances.
instance Poset Var
instance Topology Var where
    type Logic Var = Var
instance Semigroup Var
instance Module Var where
    type Scalar Var = Var

instance Show Var where
    show (Var x) = x

var1 :: Free (Sig f) '[] Var
var1 = Pure $ Var "var1"

var2 :: Free (Sig f) '[] Var
var2 = Pure $ Var "var2"

var3 :: Free (Sig f) '[] Var
var3 = Pure $ Var "var3"

var4 :: Free (Sig f) '[ 'Scalar ] Var
var4 = Pure $ Var "var4"

data Law (alg::Type->Constraint) = forall t. Law
    { lawName :: String
    , lhs :: Free (Sig alg) '[] Var
    , rhs :: Free (Sig alg) '[] Var
    }

instance Show (Free (Sig alg) '[] Var) => Show (Law alg) where
    show (Law lawName lhs rhs) = show lhs ++ " = " ++ show rhs

--------------------

reassoc :: (ViewPoset alg t, TypeConstraints t a) => Free (Sig alg) t a -> Free (Sig alg) t a
reassoc (Expr_inf (Expr_inf e1 e2) e3) = Expr_inf e1 $ reassoc (Expr_inf e2 e3)
reassoc e = e

func :: Topology a => a -> a -> Logic a
func x y = (x==x)&&(x==y)&&(y==y)

liberate1 :: (Expr alg x1                               -> y) -> x1             -> y
liberate1 f x1          = f (Pure x1)

liberate2 :: (Expr alg x1 -> Expr alg x2                -> y) -> x1 -> x2       -> y
liberate2 f x1 x2       = f (Pure x1) (Pure x2)

liberate3 :: (Expr alg x1 -> Expr alg x2 -> Expr alg x3 -> y) -> x1 -> x2 -> x3 -> y
liberate3 f x1 x2 x3    = f (Pure x1) (Pure x2) (Pure x3)

frock2 ::
    ( alg y'
    , FAlgebra alg
    ) => (y -> Free (Sig alg) t y')
      -> (Expr alg x1 -> Expr alg x2 ->       y )
      -> (         x1 ->          x2 -> App t y')
frock2 f g = \x y -> eval $ f $ liberate2 g x y

-- FIXME:
-- The names for the functions above are really weird and should be improved.

-- FIXME:
-- How does frocking affect the performance of the function?
-- Would it have the same core as the hand written code?

--------------------------------------------------------------------------------

-- NOTE:
-- There's no hope for expression trees based on the type of `a` rather than `alg`.
-- This is because the pattern/view encoding we've switched to allows only a single instance of each class.
-- A workaround is to create a class that has the exact properties of the given type.
-- I think this is only going to be possible with template haskell though.
-- I don't think the loss of expression trees for types is a big deal;
-- I can't actually think of any use cases.

-- class Universal x
-- instance Universal x
--
-- type family View (alg1::Type->Constraint) :: (Type->Constraint) -> [AT] -> Constraint
-- type instance View Poset = ViewPoset
--
-- instance ViewPoset Universal '[] where
-- --     toSigPoset (U s) = s
-- --     fromSigPoset s = U s
--
-- instance FAlgebra Universal where
--     data Sig Universal t a where
--         U :: (FAlgebra alg, View alg Universal t) => Sig alg t a -> Sig Universal t a
--
-- --     alg p (U s) = alg p s
-- --     algTag p (U s) = algTag p s
--
--     mape f (U s) = U $ mape f s
--
-- instance Show a => Show (Sig Universal t a) where

--------------------------------------------------------------------------------

instance FAlgebra Poset where
    data Sig Poset t a where
        Si :: a -> a -> Sig Poset '[] a
    alg    _ (Si a1 a2) = inf a1 a2
    algTag _ _          = error "Poset.algTag should not be constructible"

    mape f (Si e1 e2) = Si (f e1) (f e2)

--------------------

-- NOTE:
-- We could create a single View class (as shown below) to replace the View* classes we're creating for each FAlgebra.
-- This reduces the number of classes we have to create at the expense of requiring manual annotation of some type signatures.
-- The user would never have to manually add these type signatures, so it's probably the right tradeoff.
-- But it makes explaining the plumbing just a bit more wonky.

-- class (FAlgebra alg1, FAlgebra alg2, Prereq alg1 t1 alg2 t2) => ViewAll alg1 t1 alg2 t2 where
--     type Prereq alg1 t1 alg2 t2 :: Constraint
--     type Prereq alg1 t1 alg2 t2 = ()
--     toSig1   :: Sig alg2 t2 a -> Sig alg1 t1 a
--     fromSig1 :: Sig alg1 t1 a -> Sig alg2 t2 a

class FAlgebra alg => ViewPoset alg t where
    fromSigPoset :: Sig Poset '[] (      a) -> Sig alg    t         a
    toSigPoset   :: Sig alg     t        a  -> Sig Poset '[] (      a)

instance ViewPoset Poset '[] where
    fromSigPoset = P.id
    toSigPoset = P.id

pattern Sig_inf e1 e2 <- (toSigPoset -> Si e1 e2) where
    Sig_inf e1 e2 = fromSigPoset $ Si e1 e2

pattern Expr_inf ::
    ( ViewPoset alg t
    , TypeConstraints t a
    ) => Free (Sig alg) t a
      -> Free (Sig alg) t a
      -> Free (Sig alg) t a
pattern Expr_inf e1 e2 <- Free (toSigPoset -> Si e1 e2) where
    Expr_inf e1 e2 = Free $ fromSigPoset $ Si e1 e2

instance (ViewPoset alg t, TypeConstraints t a) => Poset (Free (Sig alg) t a) where
    inf = Expr_inf

--------------------

instance Variety Poset where
    laws =
        [ Law
            { lawName = "associative"
            , lhs = (var1&&var2)&&var3
            , rhs = var1&&(var2&&var3)
            }
        , Law
            { lawName = "commutative"
            , lhs = var1&&var2
            , rhs = var2&&var1
            }
        ]

--------------------

instance Show a => Show (Sig Poset '[] a) where
    show (Si a1 a2) = show a1++"&&"++show a2

----------------------------------------

instance FAlgebra Topology where
    data Sig Topology t a where
        ST :: {-#UNPACK#-}!(Sig Poset '[] a) -> Sig Topology '[ 'Logic] a
--         ST :: {-#UNPACK#-}!(Sig Poset t a) -> Sig Topology ('Logic ': t) a
        Se :: a -> a -> Sig Topology '[ 'Logic] a

    alg (p::proxy a) (ST s) = alg (Proxy::Proxy (Logic a)) s
    algTag p (Se a1 a2) = a1==a2

    mape f (ST s) = ST $ mape f s
    mape f (Se e1 e2) = Se (f e1) (f e2)

--------------------

class ViewPoset alg t => ViewTopology alg t where
    toSigTopology   :: Sig alg              t   a -> Sig Topology '[ 'Logic ] a
    fromSigTopology :: Sig Topology '[ 'Logic ] a -> Sig alg            t     a

instance ViewTopology Topology '[ 'Logic ] where
    toSigTopology = P.id
    fromSigTopology = P.id

pattern Sig_equals e1 e2 <- (toSigTopology -> Se e1 e2) where
    Sig_equals e1 e2 = fromSigTopology $ Se e1 e2

pattern Expr_equals ::
    ( ViewTopology alg ('Logic ': t)
    , TypeConstraints t a
    ) => Free (Sig alg) t a
      -> Free (Sig alg) t a
      -> Free (Sig alg) ('Logic ': t) a
pattern Expr_equals e1 e2 <- FreeTag (toSigTopology -> Se e1 e2) where
    Expr_equals e1 e2 = FreeTag $ fromSigTopology $ Se e1 e2

instance
    ( TypeConstraints t a
    , ViewTopology alg ('Logic ': t)
    ) => Topology (Free (Sig alg) t a)
        where
    type Logic (Free (Sig alg) t a) = Free (Sig alg) ('Logic  ': t) a
    (==) = Expr_equals

--------------------

instance ViewPoset Topology '[ 'Logic ] where
    toSigPoset (ST s) =  s
    fromSigPoset s = ST s

--------------------

instance (Show (Logic a), Show a) => Show (Sig Topology t a) where
    show (ST a) = show a
    show (Se a1 a2) = show a1++"=="++show a2

instance {-#OVERLAPS#-} Show (Sig Topology (t1 ': t2 ': t3 ': t) a) where
    show _ = "<<overflow>>"

----------------------------------------

instance FAlgebra Semigroup where
    data Sig Semigroup t a where
        SS :: {-#UNPACK#-}!(Sig Topology t a) -> Sig Semigroup t a
        Sa :: a -> a -> Sig Semigroup '[] a

    algTag p (SS s)     = algTag p s
    alg    p (SS s)     = alg    p s
    alg    p (Sa a1 a2) = a1+a2

    mape f (SS s) = SS $ mape f s
    mape f (Sa e1 e2) = Sa (f e1) (f e2)

--------------------

class ViewTopology alg ('Logic ': t) => ViewSemigroup alg t where
    toSigSemigroup   :: Sig alg t a -> Sig Semigroup '[] (      a)
    fromSigSemigroup :: Sig Semigroup '[] (      a) -> Sig alg t a

instance ViewSemigroup Semigroup '[] where
    toSigSemigroup = P.id
    fromSigSemigroup = P.id

pattern Sig_plus e1 e2 <- (toSigSemigroup -> Sa e1 e2) where
    Sig_plus e1 e2 = fromSigSemigroup $ Sa e1 e2

pattern Expr_plus ::
    ( ViewSemigroup alg t
    , TypeConstraints t a
    ) => Free (Sig alg) t a
      -> Free (Sig alg) t a
      -> Free (Sig alg) t a
pattern Expr_plus e1 e2 <- Free (toSigSemigroup -> Sa e1 e2) where
    Expr_plus e1 e2 = Free $ fromSigSemigroup $ Sa e1 e2

instance
    ( TypeConstraints t a
    , ViewSemigroup alg t
    ) => Semigroup (Free (Sig alg) t a)
        where
    (+) = Expr_plus

--------------------

instance ViewTopology Semigroup '[ 'Logic ] where
    toSigTopology (SS s) = s
    fromSigTopology s = SS s

instance ViewPoset Semigroup '[ 'Logic ] where
    toSigPoset (SS (toSigPoset -> s)) = s
    fromSigPoset s = SS $ fromSigPoset s

--------------------

instance (Show (Logic a), Show a) => Show (Sig Semigroup t a) where
    show (SS s) = show s
    show (Sa a1 a2) = show a1++"+"++show a2

instance {-#OVERLAPS#-}
    Show (Sig Semigroup '[ 'Logic, t1,t2,t3 ] a) where
    show _ = "<<overflow>>"

----------------------------------------

instance FAlgebra Module where
    data Sig Module t a where
        SM  :: {-#UNPACK#-}!(Sig Semigroup t          a) -> Sig Module t                   a
        SN1 :: {-#UNPACK#-}!(Sig Module    '[ t     ] a) -> Sig Module '[ t     ,'Scalar ] a
        SN2 :: {-#UNPACK#-}!(Sig Module    '[       ] a) -> Sig Module '[        'Scalar ] a
        Sp :: Scalar a -> a -> Sig Module '[] a

    alg    p            (SM s)     = alg p                         s
    alg    (p::proxy a) (SN1 s)    = alg (Proxy::Proxy (Scalar a)) s
    alg    (p::proxy a) (SN2 s)    = alg (Proxy::Proxy (Scalar a)) s
    alg    p            (Sp a1 a2) = a1.*a2

    algTag p            (SM  s) = algTag p s
    algTag (p::proxy a) (SN1 s) = algTag (Proxy::Proxy (Scalar a)) s
--     algTag (p::proxy a) (SN2 s) = algTag (Proxy::Proxy (Scalar a)) s

    mape f (SM  s) = SM  $ mape f s
    mape f (SN1 s) = SN1 $ mape f s
    mape f (SN2 s) = SN2 $ mape f s
    mape f (Sp a1 a2) = Sp (f a1) (f a2)

--------------------

class ViewSemigroup alg t => ViewModule alg t where
    toSigModule :: Sig alg t a -> Sig Module '[] (      a)
    fromSigModule :: Sig Module '[] (      a) -> Sig alg t a

instance ViewModule Module '[] where
    toSigModule = P.id
    fromSigModule = P.id

instance ViewModule Module '[ 'Scalar ] where
    toSigModule (SN2 s) = s
    fromSigModule s = SN2 s

pattern Sig_dotmul e1 e2 <- (toSigModule -> Sp e1 e2) where
    Sig_dotmul e1 e2 = fromSigModule $ Sp e1 e2

pattern Expr_dotmul ::
    ( ViewModule alg t
    , TypeConstraints t a
    ) => Free (Sig alg) (AppScalar t) a
      -> Free (Sig alg) t a
      -> Free (Sig alg) t a
pattern Expr_dotmul e1 e2 <- Free (toSigModule -> Sp e1 e2) where
    Expr_dotmul e1 e2 = Free $ fromSigModule $ Sp e1 e2

instance
    ( TypeConstraints t a
    , ViewModule alg t
    , ViewModule alg (AppScalar t)
    , AppScalar (AppScalar t) ~ AppScalar t
    , Scalar (Scalar (App t a)) ~ Scalar (App t a)
    ) => Module (Free (Sig alg) t a)
        where
    -- type Scalar (Free (Sig alg) t a) = Free (Sig alg) ('Scalar ': t) a
    type Scalar (Free (Sig alg) t a) = Free (Sig alg) (AppScalar t) a
    (.*) = Expr_dotmul

--------------------

instance ViewSemigroup Module '[] where
    toSigSemigroup (SM s) = s
    fromSigSemigroup s = SM s

instance ViewSemigroup Module '[ 'Scalar ] where
    toSigSemigroup (SN2 (SM s)) = s
    fromSigSemigroup s = SN2 $ SM s

instance ViewTopology Module '[ 'Logic ] where
    toSigTopology (SM (toSigTopology -> s)) = s
    fromSigTopology s = SM $ fromSigTopology s

instance ViewPoset Module '[ 'Logic ] where
    toSigPoset (SM (toSigPoset -> s)) = s
    fromSigPoset s = SM $ fromSigPoset s

instance ViewPoset Module '[ 'Logic, 'Scalar ] where
    toSigPoset (SN1 (toSigPoset -> s)) = s
    fromSigPoset s = SN1 $ fromSigPoset s

instance ViewTopology Module '[ 'Logic, 'Scalar ] where
    toSigTopology (SN1 (toSigTopology -> s)) = s
    fromSigTopology s = SN1 $ fromSigTopology s

--------------------

instance
    ( Show a
    , Show (Scalar a)
    , Show (Logic a)
    , Show (Logic (Scalar a))
    , Scalar (Scalar a) ~ Scalar a
    ) => Show (Sig Module t a)
        where
    show (SM s) = show s
    show (SN1 s) = show s
    show (SN2 s) = show s
    show (Sp a1 a2) = show a1++".*"++show a2

instance {-#OVERLAPS#-} Show (Sig Module (t1 ': t2 ': t3 ': ts) a) where show _ = "<<overflow>>"

----------------------------------------

instance FAlgebra Hilbert where
    data Sig Hilbert t a where
        SH :: {-#UNPACK#-}!(Sig Module t a) -> Sig Hilbert t a
        Sd :: a -> a -> Sig Hilbert '[ 'Scalar ] a

    alg    p (SH s) = alg    p s
    algTag p (SH s) = algTag p s
    algTag p (Sd a1 a2) = a1<>a2

    mape f (SH s) = SH $ mape f s
    mape f (Sd a1 a2) = Sd (f a1) (f a2)

--------------------

class ViewModule alg t => ViewHilbert alg t where
    toSigHilbert   :: Sig alg      t           a -> Sig Hilbert '[ 'Scalar ] a
    fromSigHilbert :: Sig Hilbert '[ 'Scalar ] a -> Sig alg      t           a

instance ViewHilbert Hilbert '[ 'Scalar ] where
    toSigHilbert = P.id
    fromSigHilbert = P.id

pattern Sig_dp e1 e2 <- (toSigHilbert -> Sd e1 e2) where
    Sig_dp e1 e2 = fromSigHilbert $ Sd e1 e2

pattern Expr_dp ::
    ( ViewHilbert alg ('Scalar ': t)
    , TypeConstraints t a
    ) => Free (Sig alg) t a
      -> Free (Sig alg) t a
      -> Free (Sig alg) ('Scalar ': t) a
pattern Expr_dp e1 e2 <- FreeTag (toSigHilbert -> Sd e1 e2) where
    Expr_dp e1 e2 = FreeTag $ fromSigHilbert $ Sd e1 e2

instance
    ( TypeConstraints t a
    , ViewModule alg t
    , ViewHilbert alg (AppScalar t)
    , AppScalar (AppScalar t) ~ AppScalar t
    , Scalar (Scalar (App t a)) ~ Scalar (App t a)
    , AppScalar t ~ ('Scalar ': t)
    ) => Hilbert (Free (Sig alg) t a)
        where
    (<>) = Expr_dp

--------------------

instance ViewPoset Hilbert '[ 'Logic ] where
    toSigPoset (SH (toSigPoset -> s)) = s
    fromSigPoset s = SH $ fromSigPoset s

instance ViewTopology Hilbert '[ 'Logic ] where
    toSigTopology (SH (toSigTopology -> s)) = s
    fromSigTopology s = SH $ fromSigTopology s

instance ViewSemigroup Hilbert '[ ] where
    toSigSemigroup (SH (toSigSemigroup -> s)) = s
    fromSigSemigroup s = SH $ fromSigSemigroup s

instance ViewModule Hilbert '[ ] where
    toSigModule (SH (toSigModule -> s)) = s
    fromSigModule s = SH $ fromSigModule s

instance ViewPoset Hilbert '[ 'Logic, 'Scalar ] where
    toSigPoset (SH (toSigPoset -> s)) = s
    fromSigPoset s = SH $ fromSigPoset s

instance ViewTopology Hilbert '[ 'Logic, 'Scalar ] where
    toSigTopology (SH (toSigTopology -> s)) = s
    fromSigTopology s = SH $ fromSigTopology s

instance ViewSemigroup Hilbert '[ 'Scalar ] where
    toSigSemigroup (SH (toSigSemigroup -> s)) = s
    fromSigSemigroup s = SH $ fromSigSemigroup s

instance ViewModule Hilbert '[ 'Scalar ] where
    toSigModule (SH (toSigModule -> s)) = s
    fromSigModule s = SH $ fromSigModule s

--------------------

instance
    ( Show a
    , Show (Logic a)
    , Show (Scalar a)
    , Show (Logic (Scalar a))
    , Scalar (Scalar a) ~ Scalar a
    ) => Show (Sig Hilbert t a)
        where
    show (SH s) = show s
    show (Sd a1 a2) = show a1++"<>"++show a2

instance {-#OVERLAPS#-} Show (Sig Hilbert (t1 ': t2 ': t3 ': ts) a) where show _ = "<<overflow>>"

--------------------------------------------------------------------------------

data AT
    = Scalar
    | Logic

type family App (t::k) (a::Type) ::  Type
type instance App '[]           a = a
type instance App ((x::AT)':xs) a = App x (App xs a)
type instance App 'Scalar a = Scalar a
type instance App 'Logic  a = Logic  a

type family Snoc (xs :: [k]) (y::k) where
    Snoc '[]       y = '[y]
    Snoc (x ': xs) y = x ': (Snoc xs y)

type family (++) (xs1:: [x]) (xs2:: [x]) :: [x] where
    '[] ++ '[] = '[]
    '[] ++ xs2 = xs2
    xs1 ++ '[] = xs1
    (x ': xs1) ++ xs2 = x ': (xs1++xs2)
