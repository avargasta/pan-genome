{-@ LIQUID "--reflection" @-}

-- | Core type definitions for FM-Index
module FMIndex.Types where

import Data.RList
import FMIndex.Tables (cLookup, occLookup, offsetTable)

-- | FM-Index data structure
data FMIndex = FMIndex
  { bwt  :: [Char]              -- ^ Burrows-Wheeler Transform of the text
  , ctab :: [(Char, Int)]       -- ^ C table: cumulative character counts
  , occtab  :: [(Char, [Int])]  -- ^ Occurrence table: counts of characters up to each position
  , sa   :: [Int]               -- ^ Suffix Array: indices of sorted suffixes
  , inv  :: Char -> Int -> ()   -- ^ Invariant: ensures consistency of tables with BWT
  , offsetBound :: Char -> Range -> [(Char, Int)] -> ()
    -- ^ Bidirectional BWT partition theorem (Lam et al. 2009): the
    -- occurrences of a symbol, together with everything smaller than it,
    -- within a range, never exceed that range's width. Pinned to
    -- 'FMIndex.Tables.offsetTable' -- the same traversal BiFMIndex's offset
    -- computation actually runs -- so it can only be invoked against a
    -- value the algorithm really computed, not an arbitrary Nat. Assumed
    -- via 'undefined' at construction (see FMIndex.FMIndex.buildFMIndex);
    -- deriving it for real would mean reflecting
    -- 'FMIndex.Tables.buildOccList' and proving it by induction on BWT
    -- positions instead.
  , saLen :: ()
    -- ^ The suffix array has exactly as many entries as the BWT. Lets
    -- 'FMIndex.Search.locate' be called with a bound already known against
    -- 'bwt' (as tracked by e.g. BiFMIndex's range invariant) without
    -- re-deriving it against 'sa' every time. Assumed via 'undefined' at
    -- construction, same as 'inv'/'offsetBound'; both 'FMIndex.BWT.buildBWT'
    -- and 'FMIndex.BWT.buildSA' are already independently proven to return
    -- 'len t + 1' entries, so this is a real fact, just not one wired up
    -- through reflection here.
  }

{-@ data FMIndex = FMIndex
   { bwt  :: {v:[Char] | 1 <= len v }
   , ctab :: [(Char, {v:Nat | v <= len bwt })]
  , occtab  :: [(Char, {xs:SortedList Nat | len bwt + 1 == len xs})]
   , sa   :: [Nat]
   , inv  :: c:Char -> i:{Nat | i <= len bwt} -> {v:() | cLookup c ctab + occLookup c i occtab  <= len bwt}
   , offsetBound :: symbol:Char -> rng:{v:Range | hi v <= len bwt} -> ks:[(Char,Nat)]
       -> { offsetTable symbol (lo rng) (hi rng) ks occtab
            + (occLookup symbol (hi rng) occtab - occLookup symbol (lo rng) occtab)
            <= hi rng - lo rng }
   , saLen :: {v:() | len sa == len bwt}
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