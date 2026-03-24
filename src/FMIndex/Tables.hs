-- | Functions to build and access FM-Index auxiliary tables
module FMIndex.Tables
  ( cTable
  , occTable
  , cLookup
  , occLookup
  ) where

import Data.List (sort, nub)
import FMIndex.BWT (buildBWT)

-- | Wrapper so that LH knows the length of [0..n]
{-@ assume enumFromTo' :: lo:Int -> hi:Int -> {v:[Int] | len v == (if hi >= lo then hi - lo + 1 else 0)} @-}
enumFromTo' :: Int -> Int -> [Int]
enumFromTo' = enumFromTo

-- | Wrapper so that LH knows the length of a list comprehension
{-@ assume mapLen :: f:(Int -> a) -> xs:{v:[Int] | len v == len xs} -> {v:[a] | len v == len xs} @-}
mapLen :: (Int -> a) -> [Int] -> [a]
mapLen f xs = map f xs

-- | Build C table: cumulative counts of each character
cTable :: [Char] -> [(Char, Int)]
cTable s = go (sort s) 0 []
  where
    go [] _ acc = acc
    go (x:xs) i acc
      | x `elem` map fst acc = go xs (i+1) acc
      | otherwise             = go xs (i+1) ((x,i):acc)

-- | Count occurrences of a character up to a given index
occ :: [Char] -> Char -> Int -> Int
occ l c i = length (filter (== c) (take i l))

-- | Build occurrence table: for each character, store counts up to each position
{-@ occTable :: s:{v:[Char] | len v > 0} 
             -> [(Char, {v:[Int] | len v == len s + 2})] @-}
occTable :: [Char] -> [(Char,[Int])]
occTable s = [(c, occList c) | c <- alphabet]
  where
    l        = buildBWT s          -- len l == len s + 1
    alphabet = nub l
    n        = length l            -- n == len s + 1
    indices  = enumFromTo' 0 n     -- len indices == n + 1 == len s + 2
    occList c = mapLen (occ l c) indices

-- | Lookup character in C table; return 0 if not found
cLookup :: Char -> [(Char,Int)] -> Int
cLookup c table = case lookup c table of
    Just v  -> v
    Nothing -> 0

-- | Lookup occurrence count in occ table; return 0 if not found
{-@ occLookup :: c:Char 
              -> i:{v:Int | v >= 0} 
              -> table:[(Char, {v:[Int] | len v > i})] 
              -> Int @-}
occLookup :: Char -> Int -> [(Char,[Int])] -> Int
occLookup c i table =
  case lookup c table of
    Just xs -> xs !! i
    Nothing -> 0
  