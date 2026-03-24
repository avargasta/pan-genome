-- | Functions for computing the Burrows-Wheeler Transform (BWT)
module FMIndex.BWT
  ( rotate
  , rotations
  , buildBWT
  ) where

import FMIndex.Types
import Data.List (sort)

-- | Rotate a list left by one position
{-@ rotate :: xs:{v:[Char] | len v > 0} -> {r:[Char] | len r == len xs} @-}
rotate :: [Char] -> [Char]
rotate []     = []
rotate (x:xs) = xs ++ [x]

-- | take n over an infinite list exactly produces n elements
{-@ assume takeExact :: n:Nat -> {xs:[a] | true} -> {v:[a] | len v == n} @-}
takeExact :: Int -> [a] -> [a]
takeExact = take

-- | Compute all rotations of a list
{-@ rotations :: xs:{v:[Char] | len v > 0}
              -> {rs:[{v:[Char] | len v == len xs}] | len rs == len xs} @-}
rotations :: [Char] -> [[Char]]
rotations xs = takeExact (length xs) (iterate rotate xs)

-- | sort preserves the lengtrh of the list
{-@ assume sortPreservesLen :: Ord a => xs:[a] -> {v:[a] | len v == len xs} @-}
sortPreservesLen :: Ord a => [a] -> [a]
sortPreservesLen = sort

-- | Compute the Burrows-Wheeler Transform of a string
{-@ buildBWT :: s:[Char] -> {v:[Char] | len v == len s + 1} @-}
buildBWT :: [Char] -> [Char]
buildBWT s = map last sortedRotations
  where
    s'              = '$' : s
    rotationsList   = rotations s'
    sortedRotations = sortPreservesLen rotationsList