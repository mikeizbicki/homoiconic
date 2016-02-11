module LocalPrelude
    ( Bool(..)
--     , Int
    , Integer
    , Rational
--     , Float
--     , Double
--     , Char
    , String
    , Maybe(..)

    , undefined
    , error

    , fromInteger
    , fromRational
    , toRational

    , Show (..)
    , IO

    , map
    , concat
    , (++)
    , ($)
    , (.)

    , Num --(..)
    , Proxy (..)
    , Symbol
    , Nat
    , module GHC.Exts
    , module Data.Kind
--     , module GHC.TypeLits
    )

    where

import Prelude
import Data.Kind
import Data.Proxy
import GHC.Exts
import GHC.TypeLits
