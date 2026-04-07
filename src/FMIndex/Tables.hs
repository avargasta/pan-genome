{-@ LIQUID "--reflection"     @-}

-- | Functions to build and access FM-Index auxiliary tables
module FMIndex.Tables
  ( cTable
  , occTable
  , cLookup
  , occLookup
  ) where

import Data.List (sort, nub)
import Data.RList 
import FMIndex.BWT (buildBWT)

-- | Build C table: cumulative counts of each character
{-@ ignore cTable @-}
{-@ cTable :: s:{[Char] | len s > 0} -> [(Char, {v:Nat | v <= len s })] @-}
cTable :: [Char] -> [(Char, Int)]
cTable s = go (sort s) 0 []
  where
    -- go :: [Char] -> Int -> [(Char, Int)] -> [(Char, Int)]
    {- go :: xs:[Char] -> i:{Nat | i <= len xs +1} 
           -> acc:[(Char, {v:Nat | v <= len xs })] 
           -> [(Char, {v:Nat | v <= len xs })] @-}
    go [] _ acc = acc
    go (x:xs) i acc
      | x `elem` map fst acc = go xs (i+1) acc
      | otherwise            = go xs (i+1) ((x,i):acc)

{-@ assume sort :: xs:[a] -> {v:SortedList a | len v == len xs} @-}

-- | Count occurrences of a character up to a given index
occ :: [Char] -> Char -> Int -> Int
occ l c i = length (filter (== c) (take i l))

-- | Build occurrence table: for each character, store counts up to each position
{-@  assume occTable :: ss:{[Char] | len ss > 0} -> [(Char, {xs:SortedList Nat | len ss + 1 == len xs })] @-}
occTable :: [Char] -> [(Char,[Int])]
occTable s = map (\c -> (c, occList c)) alphabet
  where
    l        = buildBWT s             -- len l == len s + 1
    alphabet = nub l                  -- unique characters in BWT
    n        = length l               -- n == len s + 1 
    occList c = map (occ l c) [0..n]  -- len indices == n + 1 == len s + 2

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
  