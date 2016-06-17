module Homoiconic.Common.Tags
    where

import Data.Proxy
import Data.Kind

import Unsafe.Coerce

--------------------------------------------------------------------------------

-- | This type synonym represents the kind of tags.
-- Using this synonym requires the -XTypeInType extension.
--
-- NOTE:
-- We would get more type safety if this were implemented as an open kind,
-- but open kinds aren't yet implemented in GHC.
type Tag = Type

-- | Apply a single tag to a type
type family AppTag (t::Tag) (a::Type)

-- | Apply a (possibly empty) list of tags to a type
type family AppTags (t::[Tag]) (a::Type) :: Type where
    AppTags '[]       a = a
    AppTags (x ': xs) a = AppTag x (AppTags xs a)

----------------------------------------

-- | Based on the definitions of AppTag and AppTags,
-- the following type properties are guaranteed to hold.
-- GHC is not smart enough to prove them automatically, however,
-- so we provide this wrapper around unsafeCoerce.
coerce_AppTags_Snoc
    :: Proxy t
    -> Proxy s
    -> Proxy a
    -> AppTags t (AppTag s a)
    -> AppTags (t `Snoc` s) a
coerce_AppTags_Snoc _ _ _ = unsafeCoerce

-- | Based on the definitions of AppTag and AppTags,
-- the following type properties are guaranteed to hold.
-- GHC is not smart enough to prove them automatically, however,
-- so we provide this wrapper around unsafeCoerce.
coerce_AppTags_Snoc_f
    :: Proxy t
    -> Proxy s
    -> Proxy a
    -> f (AppTags (t `Snoc` s) a)
    -> f (AppTags  t (AppTag s a))
coerce_AppTags_Snoc_f _ _ _ = unsafeCoerce

-- | Append an element to the end of a type list
type family Snoc (xs :: [k]) (y::k) where
    Snoc '[]       y = '[y]
    Snoc (x ': xs) y = x ': (Snoc xs y)

-- | Concatenate two type lists
type family (++) (xs1:: [x]) (xs2:: [x]) :: [x] where
    '[] ++ '[] = '[]
    '[] ++ xs2 = xs2
    xs1 ++ '[] = xs1
    (x ': xs1) ++ xs2 = x ': (xs1++xs2)

