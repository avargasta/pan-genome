{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

-- | Functions to build and access FM-Index auxiliary tables
module FMIndex.Tables
  ( cTable
  , occTable
  , cLookup
  , occLookup
  , sumOccLookup
  , offsetTable
  , incrOccTab
  ) where

import Data.List (nub)
import Data.RList
import FMIndex.BWT (buildBWT)
import Data.ProofCombinators ((?))

-- | Build C table: cumulative counts of each character
{-@ cTable :: s:[Char] -> [(Char, {v:Nat | v <= len s})] @-}
cTable :: [Char] -> [(Char, Int)]
cTable s = go (sort s) 0 []
  where
    go :: [Char] -> Int -> [(Char, Int)] -> [(Char, Int)]
    {-@ go ::  xs:[Char] -> i:{Nat | i <= len s - len xs}
           -> acc:[(Char, {v:Nat |  v  <= i })]
           -> [(Char, {v:Nat |  v <= len s })] @-}
    go [] _ acc = acc
    go (x:xs) i acc
      | x `elem` map fst acc = go xs (i+1) acc
      | otherwise            = go xs (i+1) ((x,i):acc)

-- | Build occurrence list for a character: counts of occurrences up to each position
{-@ buildOccList :: l:[Char] -> c:Char -> {xs:SortedList Nat | len xs == len l + 1} @-}
buildOccList :: [Char] -> Char -> [Int]
buildOccList l c = go 0 l
  where
    {-@ go :: n:Nat -> xs:[Char] -> {ys:SortedList {v:Nat | n <= v} | len ys == len xs + 1} @-}
    go :: Int -> [Char] -> [Int]
    go n [] = [n]
    go n (x:xs)
      | x == c    = n : go (n + 1) xs
      | otherwise = n : go n xs

-- | Build occurrence table: for each character, store counts up to each position
{-@ occTable :: l:[Char] -> [(Char, {xs:SortedList Nat | len l + 1 == len xs})] @-}
occTable :: [Char] -> [(Char,[Int])]
occTable l = map (\c -> (c, buildOccList l c)) (alphabet l)
  where
    alphabet l = nub l -- nub returns the distinct characters in l

-- | Lookup character in C table; return 0 if not found
{-@ reflect cLookup @-}
{-@ cLookup :: Char -> [(Char,Nat)] -> Nat @-}
cLookup :: Char -> [(Char,Int)] -> Int
cLookup c table = case lookup c table of
    Just v  -> v
    Nothing -> 0

-- | Lookup occurrence count in occ table; return 0 if not found
{-@ reflect occLookup @-}
{-@ occLookup :: c:Char
              -> i:Nat
              -> table:[(Char, {v:[Nat] | len v > i})]
              -> Nat @-}
occLookup :: Char -> Int -> [(Char,[Int])] -> Int
occLookup c i table =
  case lookup c table of
    Just xs -> xs `index` i
    Nothing -> 0

-- | Same idea as 'sumOcc' would be, but walking 'ks' only to enumerate
-- characters -- each one's count is fetched from 'full' via 'occLookup'
-- instead of read directly off the row. Lets sums like the BWT partition
-- identity be stated in the same occLookup-based vocabulary as
-- 'inv'/'backwardStep'.
{-@ reflect sumOccLookup @-}
{-@ sumOccLookup :: i:Nat
                  -> ks:[(Char, {v:[Nat] | len v > i})]
                  -> full:[(Char, {v:[Nat] | len v > i})]
                  -> Nat @-}
sumOccLookup :: Int -> [(Char,[Int])] -> [(Char,[Int])] -> Int
sumOccLookup _ []            _    = 0
sumOccLookup i ((c,_):rest) full  = occLookup c i full + sumOccLookup i rest full

{-@ incrOccTab :: c:Char
         -> i:Nat
         -> j:{Nat | i <= j}
         -> table:[(Char, {v:SortedList Nat | j < len v})]
         -> { occLookup c i table <= occLookup c j table }  @-}
incrOccTab :: Char -> Int -> Int -> [(Char, [Int])] -> ()
incrOccTab c i j table = case lookup c table of
  Just xs -> incrLookUpSorted xs i j
  Nothing -> ()

-- | Sum, over the characters of `ks` that are < symbol, of the width they
-- each contribute to the range [lo,hi) -- i.e. Occ(c,hi) - Occ(c,lo) for
-- every such c. Depends only on the raw tables (not on FMIndex/Range) so
-- that it can be named from inside FMIndex's own 'FMIndex.Types.offsetBound'
-- ghost field without an import cycle.
{-@ reflect offsetTable @-}
{-@ offsetTable
      :: symbol:Char -> lo:Nat -> hi:{Nat | lo <= hi} -> ks:[(Char, Nat)]
      -> table:[(Char, {v:SortedList Nat | len v > hi})] -> Nat @-}
offsetTable :: Char -> Int -> Int -> [(Char, Int)] -> [(Char, [Int])] -> Int
offsetTable _ _ _ [] _ = 0
offsetTable symbol lo hi ((c, _):cs) table
  | c < symbol = ((occLookup c hi table - occLookup c lo table) + offsetTable symbol lo hi cs table)
                   ? incrOccTab c lo hi table
  | otherwise  =                                                  offsetTable symbol lo hi cs table

