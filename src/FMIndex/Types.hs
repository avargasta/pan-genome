{-@ LIQUID "--reflection" @-}

-- | Core type definitions for FM-Index
module FMIndex.Types where

import Data.RList
import FMIndex.Tables (cLookup, occLookup, offsetTable)

-- | FM-Index data structure
data FMIndex = FMIndex
  { bwt  :: String              -- ^ Burrows-Wheeler Transform of the text
  , ctab :: [(Char, Int)]       -- ^ C table: cumulative character counts
  , occtab  :: [(Char, [Int])]  -- ^ Occurrence table: counts of characters up to each position
  , sa   :: [Int]               -- ^ Suffix Array: indices of sorted suffixes
  , stepBound :: Char -> Int -> ()   -- ^ Bounds the LF-mapping/rank used by a single backward step: ensures consistency of tables with BWT
  , partitionBound :: Char -> Range -> [(Char, Int)] -> () --The occurrences of a symbol, together with everything smaller than it, within a range, never exceed that range's width.
  }

{-@ data FMIndex = FMIndex
   { bwt  :: {v:String | 1 <= len v }
   , ctab :: [(Char, {v:Nat | v <= len bwt })]
  , occtab  :: [(Char, {xs:SortedList Nat | len bwt + 1 == len xs})]
   , sa   :: {v:[Nat] | len v == len bwt }
   , stepBound :: c:Char -> i:{Nat | i <= len bwt} -> {v:() | cLookup c ctab + occLookup c i occtab  <= len bwt}
   , partitionBound :: symbol:Char -> rng:{v:Range | hi v <= len bwt} -> ks:[(Char,Nat)]
       -> { lo rng + offsetTable symbol (lo rng) (hi rng) ks occtab
            + (occLookup symbol (hi rng) occtab - occLookup symbol (lo rng) occtab)
            <= hi rng }
   } @-}

instance Show FMIndex where
  show fidx = "FMIndex { bwt = " ++ show (bwt fidx)
           ++ ", ctab = " ++ show (ctab fidx)
           ++ ", occtab = " ++ show (occtab fidx)
           ++ ", sa = " ++ show (sa fidx)
           ++ " }"

-- | A search range [lo, hi] into a BWT/suffix array, as its own type so
-- that "lo <= hi" is guaranteed by construction rather than repeated in
-- every refinement that mentions a range.
data Range = Range { lo :: Int, hi :: Int }

{-@ data Range = Range { lo :: Nat, hi :: {v:Nat | lo <= v} } @-}

instance Show Range where
  show (Range l h) = "(" ++ show l ++ ", " ++ show h ++ ")"