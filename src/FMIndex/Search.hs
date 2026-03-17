{-@ LIQUID "--no-termination" @-}

-- | Exact backward search using FM-Index
module FMIndex.Search
  ( backwardSearch
  ) where

import FMIndex.Types
import FMIndex.Tables (cLookup, occLookup)

-- | Perform backward search of a pattern in FM-Index
-- Returns a range (sp, ep) in the BWT where the pattern occurs
backwardSearch :: String -> FMIndex -> (Int, Int)
backwardSearch pattern (FMIndex l ctab occTab) = go n ctab (reverse pattern) 1 (n-1)
  where
    n = length l

    -- Recursive helper function
{-@ go :: n:{v:Int | 0 < v } -> occTab':[(Char,{v:[Int] | len v == n})] -> [Char] -> lo:{Int | 1 <= lo && lo - 1 < n} -> hi:{Int | lo <= hi && hi < n} -> (Int, Int) @-}
    go :: Int -> [(Char, [Int])] -> [Char] -> Int -> Int -> (Int, Int)
    go _ occTab' [] lo hi = (lo, hi)  -- Base case: no more characters left
    go n occTab' (c:cs) lo hi
      | lo >= hi  = (1,0)  -- No match
      | otherwise =
          let lo' = cLookup c ctab + occLookup c (lo-1) occTab'
              hi' = cLookup c ctab + occLookup c hi occTab' - 1
          in go n occTab' cs lo' hi'