{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-termination"     @-}

-- | Functions to build and access FM-Index auxiliary tables
module FMIndex.Tables
  ( cTable
  , occTable
  , cLookup
  , occLookup
  ) where

import Data.List (nub)
import Data.RList 
import FMIndex.BWT (buildBWT)

-- | Build C table: cumulative counts of each character
{-@ cTable :: s:{[Char] | len s > 0} -> [(Char, {v:Nat | v <= len s})] @-}
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
{-@ occTable :: ss:{[Char] | len ss > 0} -> [(Char, {xs:SortedList Nat | len ss + 1 == len xs})] @-}
occTable :: [Char] -> [(Char,[Int])]
occTable l = map (\c -> (c, buildOccList l c)) alphabet
  where
    alphabet = nub l           -- unique characters in BWT

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
  