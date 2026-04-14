-- | Functions for computing the Burrows-Wheeler Transform (BWT)
module FMIndex.BWT
  ( rotate
  , rotations
  , buildBWT
  , buildSA
  ) where

import Data.List (sort, elemIndex)
import Data.Maybe (fromMaybe)

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
    s'              = s ++ "$"
    rotationsList   = rotations s'
    sortedRotations = sortPreservesLen rotationsList



-- | elemIndex returns a valid non-negative position when present
{-@ assume elemIndexNat :: Eq a => x:a -> xs:[a] -> Maybe Nat @-}
elemIndexNat :: Eq a => a -> [a] -> Maybe Int
elemIndexNat = elemIndex

-- | Build suffix array from sorted rotations
-- Returns indices of original suffixes in sorted order
{-@ buildSA :: s:[Char] -> {v:[Nat] | len v == len s + 1} @-}
buildSA :: [Char] -> [Int]
buildSA s = map rotationIndex sortedRotations
  where
    s'              = s ++ "$"
    rotationsList   = rotations s'
    sortedRotations = sortPreservesLen rotationsList
    rotationIndex r = fromMaybe 0 (elemIndexNat r rotationsList)