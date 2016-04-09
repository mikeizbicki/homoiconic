{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Algebra5
    where

import qualified Prelude as P
import LocalPrelude hiding ((.))
import Lattice
import Tests
-- import Topology1 hiding (Lawful (..), Semigroup (..), isLawful)
-- import Union
import Category

import Test.SmallCheck.Series hiding (NonNegative)
import Test.Tasty
import qualified Test.Tasty.SmallCheck as SC
import qualified Test.Tasty.QuickCheck as QC
import Test.QuickCheck hiding (Testable,NonNegative)

import Data.Typeable
import Debug.Trace
-- import GHC.Generics

import Unsafe.Coerce

-------------------------------------------------------------------------------

instance Topology Bool where
    type Logic Bool = Bool
    (==) = (P.==)
instance Semigroup Bool where
    (+) = (P.||)

instance Topology Integer where
    type Logic Integer = Bool
    (==) = (P.==)
instance Semigroup Integer where (+) = (P.+)
instance Module Integer where
    (.*) = (P.*)
    type Scalar Integer = Integer
instance Hilbert Integer where (<>) = (P.*)

instance Topology Int where
    type Logic Int = Bool
    (==) = (P.==)
instance Semigroup Int where (+) = (P.+)
instance Module Int where
    (.*) = (P.*)
    type Scalar Int = Int
instance Hilbert Int where (<>) = (P.*)

instance (Topology a, Topology b) => Topology (a,b) where
    type Logic (a,b) = (Logic a, Logic b)
    (a1,b1)==(a2,b2) = (a1==a2,b1==b2)
instance (Semigroup a,Semigroup b) => Semigroup (a,b) where
    (a1,b1)+(a2,b2) =(a1+a2,b1+b2)
instance (Module a, Module b, Scalar a~Scalar b) => Module (a,b) where
    (a1,b1).*r =(a1.*r,b1.*r)
    type Scalar (a,b) = Scalar b
instance (Hilbert a, Hilbert b, Scalar a~Scalar b) => Hilbert (a,b) where
    (a1,b1)<>(a2,b2) =(a1<>a2)+(b1<>b2)

instance (Num a, Num b) => Num (Int,Int) where
    fromInteger i = (fromInteger i, fromInteger i)

--------------------------------------------------------------------------------

-- class (Topology (Logic a), Semigroup (Logic a)) => Topology a where
class Topology a where
    type Logic a
    (==) :: a -> a -> Logic a

class Topology a => Semigroup a where
    (+) :: a -> a -> a

class (Module (Scalar a), Semigroup a) => Module a where
    type Scalar a
    (.*) :: a -> Scalar a -> a

class Module a => Hilbert a where
    (<>) :: a -> a -> Scalar a

--------------------------------------------------------------------------------

data Box t a where
    Box :: AppAT t a -> Box t a

type family Unbox a where
    Unbox (Box t a) = AppAT t (Unbox a)
    Unbox a         = a

type family Inspect a where
    Inspect (Box t a) = a
    Inspect a         = a

type family Deep a where
    Deep (Box t a) = Deep a
    Deep a         = a

instance Topology (AppAT t a) => Topology (Box t a) where
    type Logic (Box t a) = Box (Tag 'Logic  t) a
--     (==) (Box a1) (Box a2) = undefined
    (==) (Box a1) (Box a2) = Box $ a1==a2

instance Show (AppAT t a) => Show (Box t a) where show (Box a) = show a

----------------------------------------

class IAlgebra (alg::Type->Constraint) where
    data I alg a
    runI :: alg a => I alg (Box t a) -> Box t a

data IFree f a where
    IFreeBox :: f (Box t (IFree f a)) -> IFree f (Box t a)
    IFree    :: f        (IFree f a)  -> IFree f a
    IPure    :: a                     -> IFree f a

instance
    ( Show (AppAT t a)
    , Show (f (Box t (IFree f a)))
--     , Show (f        (IFree f (Box t a)))
    ) => Show (IFree f (Box t a)) where
    show (IFreeBox f) = show f
--     show (IFree    f) = show f
    show (IPure    a) = show a

instance {-#OVERLAPS#-}
    ( Show a
    , Show (f (IFree f a))
    ) => Show (IFree f a) where
    show (IPure a) = show a
    show (IFree f) = show f

----------------------------------------

instance IAlgebra Topology where
    data I Topology a where
        Ie :: a
           -> a
           -> I Topology (Box 'Logic a)

    runI (Ie a1 a2) = Box $ a1 == a2

instance Show a => Show (I Topology a) where
    show _ = "?"

instance Show a => Show (I Topology (Box t a)) where
    show (Ie a1 a2) = "("++show a1++"=="++show a2++")"

instance Topology (IFree (I Topology) a) where
    type Logic (IFree (I Topology) a) = IFree (I Topology) (Box 'Logic a)
    (==) e1 e2 = IFreeBox $ Ie e1 e2

----------------------------------------

instance IAlgebra Semigroup where
    data I Semigroup a where
        IS :: {-#UNPACK#-}!(I Topology a) -> I Semigroup a
        Ip :: a -> a -> I Semigroup a

instance (Show a) => Show (I Semigroup a) where
-- instance (Show a, Show (I Topology a)) => Show (I Semigroup a) where
--     show (IS a) = show a
    show (Ip a1 a2) = "("++show a1++"+"++show a2++")"

instance Topology (IFree (I Semigroup) a) where
    type Logic (IFree (I Semigroup) a) = IFree (I Semigroup) (Box 'Logic a)
    (==) e1 e2 = IFreeBox $ IS $ Ie e1 e2

instance Semigroup (IFree (I Semigroup) a) where
    (+) e1 e2 = IFree $ Ip e1 e2

--------------------

-- instance P.Functor (I Topology) where
--     fmap f (Ie a1 a2) = Ie (f a1) (f a2)

fm :: (a -> b) -> I Topology (Box t a) -> I Topology (Box t b)
fm f (Ie a1 a2) = Ie (f a1) (f a2)

class Eval a where
    go :: IFree (I Topology) a -> a

instance Eval a where
    go (IPure a) = a

instance {-#OVERLAPPING#-} Topology a => Eval (Box t a) where
    go (IPure a) = a
    go (IFreeBox (Ie e1 e2)) = Box $ go e1 == go e2
--     go (IFree f) = _ f

instance {-#OVERLAPPING#-} (Topology (AppAT t2 a), Topology a) => Eval (Box t1 (Box t2 a)) where
    go (IPure a) = a
    go (IFreeBox (Ie e1 e2)) = Box $ go e1 == go e2

instance {-#OVERLAPPING#-}
    ( Topology a
    , Topology (AppAT t2 a)
    , Topology (AppAT t3 a)
    , Topology (AppAT t2 (Box t3 a))
    ) => Eval (Box t1 (Box t2 (Box t3 a)))
        where
    go (IPure a) = a
    go (IFreeBox (Ie e1 e2)) = Box $ go e1 == go e2

----------------------------------------

-- i :: Free (I Topology) (Box 'Id Int)
-- i = Pure $ Box 3

-- type L = Semigroup
type L = Topology

i :: IFree (I L) Int
i = IPure 3

j :: IFree (I L) Int
j = IPure 2

--------------------------------------------------------------------------------

-- type Lang = Semigroup
type Lang = Topology

h1 = mkH 1 :: H Lang Lang (Tag 'Id 'Id) Int
h2 = mkH 2 :: H Lang Lang (Tag 'Id 'Id) Int
-- g = mkH 2 :: H Lang Lang (Tag 'Id 'Id) Int
-- h = mkH (1,2) :: H Lang Lang (Tag 'Id 'Id) (Int,Int)
-- g = mkH (0,0) :: H Lang Lang (Tag 'Id 'Id) (Int,Int)
-- g = mkH "y" :: H Lang Lang (Tag 'Id 'Id) String

----------------------------------------

class HAlgebra (alg::Type->Constraint) where
    data H (lang::Type->Constraint) alg (t::AT) (a::Type)
    mkH :: AppAT t a -> H lang alg (Tag 'Id t) a

class HAlgebra alg => HRun lang alg (t::AT) a where
    runH :: H lang alg t a -> AppAT t a

class (HAlgebra lang, HAlgebra alg) => HSuperClass lang alg t where
--     embedH :: (alg (AppAT t a)  => (H lang alg t a -> AppAT t a))
    embedH :: ( ( HRun lang alg t a
                , alg (AppAT t a)
                ) => (H lang alg t a -> AppAT t a)
              )
           -> (lang a            => (H lang alg t a -> AppAT t a))

-- emT :: (lang ~ Topology, t~'Id)
--     => (lang a               => H lang cxt      )t a)
--     -> (Topology (AppAT t a) => H lang Topology t a)
emT ::                          H lang cxt      t a
    ->                          H lang Topology t a
emT f = unsafeCoerce f

instance HAlgebra lang => HSuperClass lang lang 'Id where
--     embedH a = a

instance HAlgebra lang => HSuperClass lang lang (Tag 'Id 'Id) where
--     embedH a = a

----------------------------------------

instance HAlgebra Topology where
    data H lang Topology t a where
        Hi :: AppAT t a -> H lang Topology (Tag 'Id t) a
        He ::
            ( HSuperClass lang cxt1 t
            , HSuperClass lang cxt2 t
            )
           => H lang cxt1     (           t) a
           -> H lang cxt2     (           t) a
           -> H lang Topology (Tag 'Logic t) a

    mkH = Hi

instance HSuperClass lang Topology t => Topology (H lang Topology t a) where
    type Logic (H lang Topology t a) = H lang Topology (Tag 'Logic t) a
    (==) e1 e2 = He e1 e2

instance
    ( lang a
    , HSuperClass lang Topology t
    , Topology (AppAT t a)
    ) => HRun lang Topology (Tag s t) a where
    runH (Hi a) = a
    runH (He
        (a1 :: H lang cxt1 t a)
        (a2 :: H lang cxt2 t a)
        ) = embedH @lang @cxt1 @t runH a1
         == embedH @lang @cxt2 @t runH a2

instance Show (H lang Topology 'Id a) where
instance {-#OVERLAPS#-}
    ( Show (AppAT t a)
    , Show (H lang Topology t a)
    ) => Show (H lang Topology (Tag s t) a)
        where
    show (Hi a) = "["++show a++"]"
    show (He a1 a2) = "("++show (emT a1)++"=="++show (emT a2)++")"

----------------------------------------

instance HSuperClass Semigroup Topology 'Id

instance HAlgebra Semigroup where
    data H lang Semigroup t a where
        HS :: {-#UNPACK#-}!(H lang Topology t a) -> H lang Semigroup t a
        Hp ::
            ( HSuperClass lang cxt 'Id
            )
           => H lang cxt       (           t) a
           -> H lang cxt       (           t) a
           -> H lang Semigroup (           t) a

    mkH = HS . mkH

-- instance Topology (H lang Semigroup t a) where
--     type Logic (H lang Semigroup t a) = H lang Semigroup (Tag 'Logic t) a
--     (==) e1 e2 = HS $ He e1 e2
--
-- instance Semigroup (H lang Semigroup t a) where
--     (+) e1 e2 = Hp e1 e2

-- instance Show (H lang Semigroup 'Id a) where
-- instance {-#OVERLAPS#-}
--     ( Show (AppAT t a)
--     , Show (H lang Semigroup t a)
--     , Show (H lang Topology  t a)
--     ) => Show (H lang Semigroup (Tag s t) a)
--         where
--     show (HS a) = show a
--     show (Hp a1 a2) = "("++show (emS a1)++"+"++show (emS a2)++")"
--
-- emS :: H lang cxt t a -> H lang Semigroup t a
-- emS = unsafeCoerce

--------------------------------------------------------------------------------

class FAlgebra (alg::Type->Constraint) where
    data F alg (t::AT) (a::Type)

    runF :: alg (AppAT t a) => F alg (Tag s t) a -> AppAT (Tag s t) a
    mkF :: AppAT t a -> F alg (Tag 'Id t) a

class (FAlgebra cxt1, FAlgebra cxt2) => EmbedF cxt1 t cxt2 where
    embedF :: F cxt2 t' a -> F cxt1 (Tag t t') a

instance FAlgebra cxt => EmbedF cxt 'Id cxt where
    embedF a = reTag a

----------------------------------------

instance FAlgebra Topology where
    data F Topology t a where
        Fi :: AppAT t a -> F Topology (Tag 'Id t) a
        Fe ::
           ( EmbedF Topology 'Id cxt1
           , EmbedF Topology 'Id cxt2
           ) => F cxt1     (Tag 'Id    t) a
             -> F cxt2     (Tag 'Id    t) a
             -> F Topology (Tag 'Logic t) a

    runF (Fi a) = a
    runF (Fe a1 a2) = runF a1' == runF a2'
        where
            a1' = embedF @Topology @'Id a1
            a2' = embedF @Topology @'Id a2

    mkF = Fi

instance Topology (F Topology t a) where
    type Logic (F Topology t a) = F Topology (Tag 'Logic t) a
    (==) e1 e2 = Fe (reTag e1) (reTag e2)

instance Show (AppAT t a) => Show (F Topology (Tag s t) a) where
    show (Fi a) = show a
    show (Fe a1 a2) = "(a"++show a1'++"=="++show a2'++")"
        where
            a1' = embedF @Topology @'Id a1
            a2' = embedF @Topology @'Id a2

----------------------------------------

instance FAlgebra Semigroup where
    data F Semigroup t a where
        FS :: {-#UNPACK#-}!(F Topology t a) -> F Semigroup t a
        Fp ::
           ( EmbedF Semigroup 'Id cxt1
           , EmbedF Semigroup 'Id cxt2
           ) => F cxt1      (Tag 'Id t) a
             -> F cxt2      (Tag 'Id t) a
             -> F Semigroup (Tag 'Id t) a

    runF (FS a) = runF a
    runF (Fp a1 a2) = runF a1' + runF a2'
        where
            a1' = embedF @Semigroup @'Id a1
            a2' = embedF @Semigroup @'Id a2

    mkF = FS . mkF

instance EmbedF Topology 'Id Semigroup where
    embedF (FS a) = reTag a
--     embedF (Fp a1 a2) = _

instance Topology (F Semigroup t a) where
    type Logic (F Semigroup t a) = F Semigroup (Tag 'Logic t) a
    (==) e1 e2 = FS $ Fe (reTag e1) (reTag e2)

instance Semigroup (F Semigroup t a) where
    (+) e1 e2 = unTag $ Fp (reTag e1) (reTag e2)

instance Show (AppAT t a) => Show (F Semigroup (Tag s t) a) where
    show (FS a) = show a
    show (Fp a1 a2) = "("++show a1'++"+"++show a2'++")"
        where
            a1' = embedF @Semigroup @'Id a1
            a2' = embedF @Semigroup @'Id a2

--------------------------------------------------------------------------------

x = mkF (1,2) :: F Semigroup (Tag 'Id 'Id) (Int,Int)
y = mkF "y" :: F Semigroup (Tag 'Id 'Id) String

--------------------

-- x = Pure (1,2) :: Expr Semigroup (Tag 'Id 'Id) (Int,Int)
-- y = Pure (3,4) :: Expr Semigroup (Tag 'Id 'Id) (Int,Int)
-- z = Pure (5,5) :: Expr Semigroup (Tag 'Id 'Id) (Int,Int)

-- x = Pure "x" :: Expr Semigroup (Tag 'Id 'Id) String
-- x = Pure "x" :: Expr Semigroup 'Id String
-- y = Pure "y" :: Expr Semigroup (Tag 'Id 'Id) String
-- z = Pure "z" :: Expr Semigroup (Tag (Tag 'Id 'Id) (Tag 'Id 'Id)) String
-- z = Pure "z" :: Expr Semigroup (Tag 'Id 'Id) String

--------------------------------------------------------------------------------

data GFree f (t::AT) e where
    GFreeTag :: f (Tag s t) (GFree f t e)  -> GFree f (Tag s t) e
    GFree    :: f        t  (GFree f t e)  -> GFree f        t  e
    GPure    :: AppAT t e                  -> GFree f        t  e

instance
    ( Show (AppAT t e)
    , Show (f t (GFree f t e))
    ) => Show (GFree f t e)
        where
    show (GPure e) = show e
    show (GFree f) = show f

g :: GFree (G lang Topology) (Tag 'Id 'Id) Int
g = GPure 1

----------------------------------------

class GAlgebra (alg::Type->Constraint) where
    data G (lang::Type->Constraint) alg (t::AT) a
    runG ::
        ( lang a
        , GSuper lang Topology t
        ) => G lang alg (Tag s t) a
          -> AppAT (Tag s t) a

class (GAlgebra lang, GAlgebra alg) => GSuper lang alg (t::AT) where
    embedG :: (alg (AppAT t a) => f)
           -> (lang a          => f)

----------------------------------------

instance GAlgebra Topology where
    data G lang Topology t a where
        Ge :: AppAT t a
           -> AppAT t a
           -> G lang Topology (Tag 'Logic t) a

    runG (Ge e1 e2 :: G lang Topology (Tag s t) a)
        = embedG @lang @Topology @t @a (e1==e2)

instance Show (AppAT t a) => Show (G lang Topology (Tag s t) a) where
    show (Ge a1 a2) = "("++show a1++"=="++show a2++")"

instance Topology (GFree (G lang Topology) t a) where
    type Logic (GFree (G lang Topology) t a) = GFree (G Lang Topology) (Tag 'Logic t) a
--     (==) e1 e2 = _GFree (Ge e1 e2)

----------------------------------------

-- instance GAlgebra Semigroup where
--     data G Semigroup t a where
--         GS :: {-#UNPACK#-}!(G Topology t a) -> G Semigroup t a
--         Gp :: AppAT (Tag 'Id t) a
--            -> AppAT (Tag 'Id t) a
--            -> G Semigroup (Tag 'Id t) a
--
--     runG (Gp e1 e2) = e1+e2
--
-- instance Show (AppAT t a) => Show (G Semigroup (Tag s t) a) where
--     show (GS a) = show a
--     show (Gp a1 a2) = "("++show a1++"+"++show a2++")"
--
-- instance
--     ( AppAT t (GFree (G Semigroup) t e)
--     ~          GFree (G Semigroup) t e
--     ) => Topology (Expr Semigroup t e) where
--     type Logic (Expr Semigroup t e) = Expr Semigroup (Tag 'Logic t) e
--     (==) e1 e2 = GFree $ GS $ Ge e1 e2
--
-- instance
--     ( AppAT t (GFree (G Semigroup) t e)
--     ~          GFree (G Semigroup) t e
--     ) => Semigroup (Expr Semigroup t e) where
--     (+) e1 e2 = unTag $ GFree $ Gp e1 e2

--------------------------------------------------------------------------------

unTag :: e (Tag t1 t2) a -> e (NestAT t1 t2) a
unTag = unsafeCoerce

reTag :: e (NestAT t1 t2) a -> e (Tag t1 t2) a
reTag = unsafeCoerce

--------------------------------------------------------------------------------

data AT
    = Id
    | Scalar
    | Logic
    | Tag AT AT

type family AppAT (t::AT) (a::Type) :: Type
type instance AppAT 'Id a = a
type instance AppAT 'Scalar a = Scalar a
type instance AppAT 'Logic  a = Logic  a
type instance AppAT (Tag t t') a = AppAT t (AppAT t' a)

type family NestAT (t::AT) (a::AT) :: AT where
    NestAT 'Id     t       = t
    NestAT t       'Id     = t
    NestAT t1      (Tag 'Id     t) = (Tag t1 t)
    NestAT s       t       = Tag s t
