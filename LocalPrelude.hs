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

    , (++)
    , ($)
    , (.)

    , Num --(..)
    , Proxy (..)
    , module GHC.Exts
    )

    where

import Prelude
import Data.Proxy
import GHC.Exts
