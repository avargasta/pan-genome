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

-- | Wrapper so that LH knows the length of [0..n]
{-@ assume enumFromTo' :: lo:Int -> hi:Int -> {v:[Int] | len v == (if hi >= lo then hi - lo + 1 else 0)} @-}
enumFromTo' :: Int -> Int -> [Int]
enumFromTo' = enumFromTo

-- | Build C table: cumulative counts of each character
cTable :: [Char] -> [(Char, Int)]
cTable s = go (sort s) 0 []
  where
    go [] _ acc = acc
    go (x:xs) i acc
      | x `elem` map fst acc = go xs (i+1) acc
      | otherwise            = go xs (i+1) ((x,i):acc)

-- | Count occurrences of a character up to a given index
occ :: [Char] -> Char -> Int -> Int
occ l c i = length (filter (== c) (take i l))

-- | Build occurrence table: for each character, store counts up to each position
{-@ occTable :: s:{v:[Char] | len v > 0} 
             -> [(Char, {v:[Int] | len v == len s + 2})] @-}
occTable :: [Char] -> [(Char,[Int])]
occTable s = map (\c -> (c, occList c)) alphabet
  where
    l        = buildBWT s          -- len l == len s + 1
    alphabet = nub l               -- unique characters in BWT
    n        = length l            -- n == len s + 1
    indices  = enumFromTo' 0 n     -- len indices == n + 1 == len s + 2
    occList c = map (occ l c) indices 

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
  