{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--reflection"     @-}

-- | Exact backward search using FM-Index
module FMIndex.Search
  ( backwardSearch
  ) where

import FMIndex.Types
import FMIndex.Tables (cLookup, occLookup)

-- | Perform backward search of a pattern in FM-Index
-- Returns a range (sp, ep) in the BWT where the pattern occurs
backwardSearch :: String -> FMIndex -> (Int, Int)
backwardSearch pattern fidx@(FMIndex l cTab occTab) = go occTab (reverse pattern) 0 (n-1)
  where

    -- Recursive helper function
    n = length l
    {-@ go :: [(Char,{v:[Nat] | len v == len l + 1})] 
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
          in go occTab cs lo' (hi' `const` theorem fidx c hi  
                                   `const` incrOccTab fidx c lo hi
                                   `const` assume (occLookup c lo occTab <= occLookup c hi occTab) () 
                                   `const` assert (lo' <= hi') () 
                                   `const` assume (hi' <= n) ()
                                   )



{-@ assert :: b:{Bool | b} -> a -> {x:a | b} @-}
assert :: Bool -> a -> a
assert _ x = x


{-@ assume assume :: b:Bool -> a -> {x:a | b} @-}
assume :: Bool -> a -> a
assume _ x = x


{-@ incrOccTab :: fmidx : FMIndex 
               -> c:Char 
               -> i:Nat
               -> j:{Nat | i <= j}
              -> { occLookup c i (occ fmidx) <= occLookup c j (occ fmidx) }  @-}
incrOccTab :: FMIndex -> Char -> Int -> Int -> ()
incrOccTab _ _ _ _ = undefined



{-@ theorem :: fmidx : FMIndex 
            -> c:Char 
            -> i:Nat
            -> {cLookup c (ctab fmidx) + occLookup c i (occ fmidx) <= len (bwt fmidx) }  @-}
theorem :: FMIndex -> Char -> Int -> ()
theorem _ _ _ = undefined 
