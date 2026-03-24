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
backwardSearch pattern (FMIndex l cTab occTab) = go occTab (reverse pattern) 0 (n-1)
  where

    -- Recursive helper function
    -- {-@ go :: n:{v:Int | 0 < v} -> [(Char,{v:[Int] | len v == n + 1})] -> [Char] -> lo:{Int | 0 <= lo} -> hi:{Int | lo <= hi && hi <= n} -> (Int, Int) @-}
    n = length l
      --  -> [(Char,{v:[Int] | len v == len l + 1})]    {v:[Int] | len v == len l + 1}
    {-@ go :: [(Char,{v:[Int] | len v == len l + 1})] -> [Char] -> lo:{Int | 0 <= lo} -> hi:{Int | lo <= hi} -> (Int, Int) @-}
    go :: [(Char, [Int])] -> [Char] -> Int -> Int -> (Int, Int)
    go occTab [] lo hi = (lo, hi)  -- Base case: no more characters left
    go occTab (c:cs) lo hi
      | lo > hi  = (1,0)  -- No match
      | otherwise =
          let lo' = cLookup c cTab + occLookup c lo occTab
              hi' = cLookup c cTab + occLookup c hi occTab
          in go occTab cs lo' hi'


--     -- Recursive helper function
-- {-@ go :: n:{v:Int | 0 < v } -> occTab':[(Char,{v:[Int] | len v == n})] -> [Char] -> lo:{Int | 1 <= lo && lo - 1 < n} -> hi:{Int | lo <= hi && hi < n} -> (Int, Int) @-}
--     go :: Int -> [(Char, [Int])] -> [Char] -> Int -> Int -> (Int, Int)
--     go _ occTab' [] lo hi = (lo, hi)  -- Base case: no more characters left
--     go n occTab' (c:cs) lo hi
--       | lo > hi  = (1,0)  -- No match
--       | otherwise =
--           let lo' = cLookup c cTab + occLookup c (lo-1) occTab'
--               hi' = cLookup c cTab + occLookup c hi occTab' - 1
--           in go n occTab' cs lo' hi'