-- | Exact backward search using FM-Index
module FMIndex.Search
  ( backwardSearch
  ) where

import FMIndex.Types
import FMIndex.Tables (cLookup, occLookup)

-- | Perform backward search of a pattern in FM-Index
-- Returns a range (sp, ep) in the BWT where the pattern occurs
backwardSearch :: String -> FMIndex -> (Int, Int)
backwardSearch pattern (FMIndex l ctab occTab) = go (reverse pattern) (0, n-1)
  where
    n = length l

    -- Recursive helper function
    go [] range = range  -- Base case: no more characters left
    go (c:cs) (sp, ep)
      | sp > ep  = (1,0)  -- No match
      | otherwise =
          let sp' = cLookup c ctab + occLookup c (sp-1) occTab
              ep' = cLookup c ctab + occLookup c ep occTab - 1
          in go cs (sp', ep')