module FMIndex.SuffixArray
  ( SA
  , buildSA
  ) where

import qualified Data.Vector.Unboxed as U

type SA = U.Vector Int

buildSA :: U.Vector Char -> SA
buildSA = undefined 