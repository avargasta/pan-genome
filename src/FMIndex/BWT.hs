-- | Functions for computing the Burrows-Wheeler Transform (BWT)
module FMIndex.BWT
  ( rotate
  , rotations
  , buildBWT
  ) where

import FMIndex.Types
import Data.List (sort)

-- | Rotate a list left by one position
{-@ rotate :: xs:{[Char] | len xs > 0} -> {v:[Char] | len v == len xs} @-}
rotate :: [Char] -> [Char]
rotate (y:ys) = ys ++ [y]

-- | Compute all rotations of a list
{-@ rotations :: {xs:[Char] | len xs > 0} -> [{v:[Char] | len v > 0}] @-}
rotations :: [Char] -> [[Char]]
rotations xs = take (length xs) (iterate rotate xs)

-- | Compute the Burrows-Wheeler Transform of a string
{-@ buildBWT :: {s:[Char] | len s > 0} -> [Char] @-}
buildBWT :: [Char] -> [Char]
buildBWT s = map last sortedRotations
  where
    rotationsList   = rotations s
    sortedRotations = sort rotationsList