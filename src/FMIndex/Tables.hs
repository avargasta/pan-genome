-- | Functions to build and access FM-Index auxiliary tables
module FMIndex.Tables
  ( cTable
  , occTable
  , cLookup
  , occLookup
  ) where

import Data.List (sort, nub)
import FMIndex.BWT (buildBWT)

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
occ l c i = length (filter (== c) (take (i+1) l))

-- | Build occurrence table: for each character, store counts up to each position
{-@ occTable :: {s:[Char] | len s > 0} -> [(Char,[Int])] @-}
occTable :: [Char] -> [(Char,[Int])]
occTable s = [(c, occList c) | c <- alphabet]
  where
    l        = buildBWT s
    alphabet = nub l
    n        = length l
    occList c = [occ l c i | i <- [0..n-1]]

-- | Lookup character in C table; return 0 if not found
cLookup :: Char -> [(Char,Int)] -> Int
cLookup c table = case lookup c table of
    Just v  -> v
    Nothing -> 0

-- | Lookup occurrence count in occ table; return 0 if not found
{-@ occLookup :: c:Char 
              -> i:{v:Int | v >= 0} 
              -> table:[(Char,[Int])] 
              -> Int @-}
occLookup :: Char -> Int -> [(Char,[Int])] -> Int
occLookup c i table =
  case lookup c table of
    Just xs -> xs !! i
    Nothing -> 0