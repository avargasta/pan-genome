-- | Functions for computing the Burrows-Wheeler Transform (BWT)
module FMIndex.BWT
  ( rotate
  , rotations
  , buildBWT
  , buildSA
  ) where

import Data.Maybe (fromMaybe)
import Data.RList (sort, iterateN, elemIndexNat)

-- | Rotate a list left by one position
{-@ rotate :: xs:{v:String | True} -> {r:String | len r == len xs} @-}
rotate :: String -> String
rotate []     = []
rotate (x:xs) = xs ++ [x]

-- | Compute all rotations of a list
{-@ rotations :: xs:{v:String | True}
              -> {rs:[{v:String | len v == len xs}] | len rs == len xs} @-}
rotations :: String -> [String]
rotations xs = iterateN rotate (length xs) xs

-- | Compute the Burrows-Wheeler Transform of a string
{-@ buildBWT :: s:String -> {v:String | len v == len s + 1} @-}
buildBWT :: String -> String
buildBWT s = map last sortedRotations
  where
    s'              = s ++ "$"
    rotationsList   = rotations s'
    sortedRotations = sort rotationsList

-- | Build suffix array from sorted rotations
-- Returns indices of original suffixes in sorted order
{-@ buildSA :: s:String -> {v:[Nat] | len v == len s + 1} @-}
buildSA :: String -> [Int]
buildSA s = map rotationIndex sortedRotations
  where
    s'              = s ++ "$"
    rotationsList   = rotations s'
    sortedRotations = sort rotationsList
    rotationIndex r = fromMaybe 0 (elemIndexNat r rotationsList)