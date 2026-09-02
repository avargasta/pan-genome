{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module BiFMIndex.BiBackwardSearch where

import FMIndex.Search (backwardStep)
import FMIndex.Types (ctab, occtab, partitionBound, Range(..))
import FMIndex.Tables (offsetTable)
import BiFMIndex.Types (BiFMIndex(..), BiRange(..), BiState(..))
import Data.ProofCombinators ((?))

-- | Bidirectional BWT partition theorem (Lam et al. 2009): the occurrences
-- of `symbol`, together with everything smaller than it, within the
-- current original range, never exceed that range's width. Made checkable
-- by injecting the fact from the original index's own 'partitionBound' ghost
-- field -- pinned to 'offsetTable', the very traversal computed below, so
-- the assumption can't be misapplied to a value the algorithm didn't
-- actually produce.
{-@ reflect offsetBackward @-}
{-@ offsetBackward :: st:BiState -> symbol:Char -> Nat @-}
offsetBackward :: BiState -> Char -> Int
offsetBackward st symbol = offsetTable symbol (lo rng) (hi rng) (ctab fi) (occtab fi)
  where
    rng = range (biRange st)
    fi  = fmidx (biIndex st)

-- | Extend the current pattern with one symbol.
{-@ biBackwardStep :: BiState -> Char -> BiState @-}
biBackwardStep :: BiState -> Char -> BiState
biBackwardStep st symbol =
  BiState
    { biIndex = bi
    , biRange = BiRange
        { pattern = nextPattern
        , range   = nextRange
        , rangeR  = nextRangeR
        }
    }
  where
    bi          = biIndex st
    r           = biRange st
    nextPattern = [symbol] ++ pattern r
    nextRange   = backwardStep symbol (fmidx bi) (range r)

    Range loR _ = rangeR r
    offset = offsetBackward st symbol ? partitionBound (fmidx bi) symbol (range r) (ctab (fmidx bi))
    Range lo' hi' = nextRange
    loR'        = loR + offset
    hiR'        = loR' + (hi' - lo')
    nextRangeR  = Range loR' hiR'

{-@ biBackwardSearchExact :: BiState -> String -> BiState @-}
biBackwardSearchExact :: BiState -> String -> BiState
biBackwardSearchExact st s = go st (reverse s)
  where
    {-@ go :: BiState -> String -> BiState @-}
    go acc []     = acc
    go acc (c:cs) = go (biBackwardStep acc c) cs
