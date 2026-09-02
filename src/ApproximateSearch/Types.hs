{-@ LIQUID "--reflection" @-}

module ApproximateSearch.Types where

import BiFMIndex.Types (BiFMIndex(..), BiRange(..))
import FMIndex.Types (ctab, Range(..))

-- ---------------------------------------------------------------------------
-- Helpers shared by prefix and suffix operations
-- ---------------------------------------------------------------------------

-- | The [start, end) window of pattern positions a branch currently covers.
type Coverage = (Int, Int)
{-@ type Coverage = (Nat, Nat) @-}

-- | A range is empty when its lower bound is not strictly below its upper
--   bound (no occurrences left).
isEmptyRange :: BiRange -> Bool
isEmptyRange r = rangeWidth r <= 0

-- | Number of occurrences currently covered by a range.
rangeWidth :: BiRange -> Int
rangeWidth r = hi (range r) - lo (range r)

-- | All alphabet characters that differ from the given one (and from the
--   sentinel '$'). These are the candidate substitutions at a mismatch.
enumerateMismatches :: BiFMIndex -> Char -> String
enumerateMismatches bi c = filter (\x -> x /= c && x /= '$') (map fst (ctab (fmidx bi)))
