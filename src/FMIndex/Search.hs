{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

-- | Exact backward search using FM-Index
module FMIndex.Search
  ( backwardSearch
  , bwtRangeToOriginal
  ) where

import Data.RList
import FMIndex.Types
import FMIndex.Tables (cLookup, occLookup)
import Data.ProofCombinators

-- | Perform backward search of a pattern in FM-Index
-- Returns a range (sp, ep) in the BWT where the pattern occurs
backwardSearch :: String -> FMIndex -> (Int, Int)
backwardSearch pattern fidx@(FMIndex l cTab occTab sa inv) = go occTab (reverse pattern) 0 n
  where

    -- Recursive helper function
    n = length l
    {-@ go :: {v:[(Char,{v:SortedList Nat | len v == len l + 1})] | v == occtab fidx} 
           -> [Char] 
           -> lo:{Int | 0 <= lo  } 
           -> hi:{Int | lo <= hi && hi <= len l } 
           -> (Int, Int) @-}
    go :: [(Char, [Int])] -> [Char] -> Int -> Int -> (Int, Int)
    go occTab [] lo hi = (lo, hi)  -- Base case: no more characters left
    go occTab (c:cs) lo hi
      | lo > hi  = (1,0)  -- No match
      | otherwise =
          let lo' = cLookup c cTab + occLookup c lo occTab {- <= than the number of times c appears -}
              hi' = cLookup c cTab + occLookup c hi occTab
          in go occTab cs lo' (hi' ? inv c hi  
                                   ? incrOccTab c lo hi occTab)

{-@ incrOccTab :: c:Char 
         -> i:Nat
         -> j:{Nat | i <= j}
         -> table:[(Char, {v:SortedList Nat | j < len v})] 
         -> { occLookup c i table <= occLookup c j table }  @-}
incrOccTab :: Char -> Int -> Int -> [(Char, [Int])] -> ()
incrOccTab c i j table = case lookup c table of
  Just xs -> incrLookUpSorted xs i j
  Nothing -> ()

-- | Convert a range of BWT indices to original text positions
-- Given a range [lo, hi) from backwardSearch, return the original positions
{-@ assume bwtRangeToOriginal :: FMIndex -> Nat -> Nat -> [Nat] @-}
bwtRangeToOriginal :: FMIndex -> Int -> Int -> [Int]
bwtRangeToOriginal fidx lo hi =
  [sa fidx !! i | i <- [lo .. hi - 1], i >= 0 && i < length (sa fidx)]