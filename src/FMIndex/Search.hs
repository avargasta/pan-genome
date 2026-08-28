{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

-- | Exact backward search using FM-Index
module FMIndex.Search
  ( backwardStep
  , backwardSearch
  , locate
  ) where

import FMIndex.Types
import FMIndex.Tables (cLookup, occLookup, incrOccTab)
import Data.ProofCombinators

-- | Extend a range by a single character -- one step of backward search.
{-@ reflect backwardStep @-}
{-@ backwardStep :: c:Char -> fidx:FMIndex -> r:{v:Range | hi v <= len (bwt fidx)}
                 -> {v:Range | hi v <= len (bwt fidx) && hi v - lo v == occLookup c (hi r) (occtab fidx) - occLookup c (lo r) (occtab fidx)} @-}
backwardStep :: Char -> FMIndex -> Range -> Range
backwardStep c fidx (Range sp ep) =
  Range (cLookup c (ctab fidx) + occLookup c sp (occtab fidx))
        (cLookup c (ctab fidx) + occLookup c ep (occtab fidx)
          ? inv fidx c ep
          ? incrOccTab c sp ep (occtab fidx))

-- | Perform backward search of a pattern in FM-Index
-- Returns a range [sp, ep] in the BWT where the pattern occurs
{-@ backwardSearch :: p:String -> fidx:FMIndex -> {v:Range | hi v <= len (bwt fidx)} -> {v:Range | hi v <= len (bwt fidx)} @-}
backwardSearch :: String -> FMIndex -> Range -> Range
backwardSearch pattern fidx r0 = go (reverse pattern) r0
  where
    {-@ go :: [Char] -> r:{v:Range | hi v <= len (bwt fidx)}
           -> {v:Range | hi v <= len (bwt fidx)} @-}
    go :: [Char] -> Range -> Range
    go []     r = r  -- Base case: no more characters left
    go (c:cs) r = go cs (backwardStep c fidx r)

-- | Convert a range of BWT indices to original text positions
-- Given a range [lo, hi) from backwardSearch, return the original positions
{-@ locate :: fidx:FMIndex -> lo:Nat -> hi:{Nat | lo < hi && hi <= len (sa fidx) } -> [Nat] @-}
locate :: FMIndex -> Int -> Int -> [Int]
locate fidx lo hi = go (hi - lo) 
   where 
      {-@ go :: i:{Nat |  hi - i < len (sa fidx) && i <= hi } -> {v:[Nat] | len v == i } @-}
      go i | i == 0   = []
           | i == 1   = [sa fidx !! (hi - 1)]
           | otherwise = sa fidx !! (hi - i) : go (i - 1)
