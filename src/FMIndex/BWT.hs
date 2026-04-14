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
{-@ rotate :: xs:{v:[Char] | len v > 0} -> {r:[Char] | len r == len xs} @-}
rotate :: [Char] -> [Char]
rotate []     = []
rotate (x:xs) = xs ++ [x]

-- | Compute all rotations of a list
{-@ rotations :: xs:{v:[Char] | len v > 0}
              -> {rs:[{v:[Char] | len v == len xs}] | len rs == len xs} @-}
rotations :: [Char] -> [[Char]]
rotations xs = iterateN rotate (length xs) xs

-- | Compute the Burrows-Wheeler Transform of a string
{-@ buildBWT :: s:[Char] -> {v:[Char] | len v == len s + 1} @-}
buildBWT :: [Char] -> [Char]
buildBWT s = map last sortedRotations
  where
    s'              = s ++ "$"
    rotationsList   = rotations s'
    sortedRotations = sort rotationsList


-- | Build suffix array from sorted rotations
-- Returns indices of original suffixes in sorted order
{-@ buildSA :: s:[Char] -> {v:[Nat] | len v == len s + 1} @-}
buildSA :: [Char] -> [Int]
buildSA s = map rotationIndex sortedRotations
  where
    s'              = s ++ "$"
    rotationsList   = rotations s'
    sortedRotations = sort rotationsList
    rotationIndex r = fromMaybe 0 (elemIndexNat r rotationsList)