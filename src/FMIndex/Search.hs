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
{-@ backwardSearch :: p:String -> fidx:FMIndex -> {v:(Nat, Nat) | fst v <= snd v && snd v <= len (bwt fidx) } -> {v:(Nat, Nat) | fst v <= snd v} @-}
backwardSearch :: String -> FMIndex -> (Int, Int) -> (Int, Int)
backwardSearch pattern fidx@(FMIndex l cTab occTab sa inv) (lo, hi) = go occTab (reverse pattern) lo hi
  where

    -- Recursive helper function
    n = length l
    {-@ go :: {v:[(Char,{v:SortedList Nat | len v == len l + 1})] | v == occtab fidx} 
           -> [Char] 
           -> lo:Nat
           -> hi:{Nat | hi <= len l && lo <= hi } 
           -> {v:(Nat, Nat) | fst v <= snd v} @-}
    go :: [(Char, [Int])] -> [Char] -> Int -> Int -> (Int, Int)
    go occTab [] lo hi = (lo, hi)  -- Base case: no more characters left
    go occTab (c:cs) lo hi
      | lo > hi  = (0,0)  -- No match
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
{-@ bwtRangeToOriginal :: fidx:FMIndex -> lo:Nat -> hi:{Nat | lo < hi && hi <= len (sa fidx) } -> [Nat] @-}
bwtRangeToOriginal :: FMIndex -> Int -> Int -> [Int]
bwtRangeToOriginal fidx lo hi = go (hi - lo) 
   where 
      {-@ go :: i:{Nat |  hi - i < len (sa fidx) && i <= hi } -> {v:[Nat] | len v == i } @-}
      go i | i == 0   = []
           | i == 1   = [sa fidx !! (hi - 1)]
           | otherwise = sa fidx !! (hi - i) : go (i - 1)
