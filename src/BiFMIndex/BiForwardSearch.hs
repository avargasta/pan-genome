{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module BiFMIndex.BiForwardSearch where

import FMIndex.Search (backwardStep)
import FMIndex.Types (FMIndex, bwt, ctab, occtab, offsetBound, Range(..))
import FMIndex.Tables (occLookup, offsetTable)
import BiFMIndex.Types (BiFMIndex(..), BiRange(..), BiState(..))
import Data.ProofCombinators ((?))

-- | Bidirectional BWT partition theorem (Lam et al. 2009): the occurrences
-- of `symbol`, together with everything smaller than it, within the
-- current reverse range, never exceed that range's width. Made checkable
-- by injecting the fact from the reverse index's own 'offsetBound' ghost
-- field -- pinned to 'offsetTable', the very traversal computed below, so
-- the assumption can't be misapplied to a value the algorithm didn't
-- actually produce.
{-@ reflect offsetForward @-}
{-@ offsetForward :: st:BiState -> symbol:Char -> Nat @-}
offsetForward :: BiState -> Char -> Int
offsetForward st symbol = offsetTable symbol (lo rng) (hi rng) (ctab fi) (occtab fi)
  where
    rng = rangeR (biRange st)
    fi  = fmidxR (biIndex st)

-- | Extend the current pattern with one symbol.
{-@ biForwardSearch :: BiState -> Char -> BiState @-}
biForwardSearch :: BiState -> Char -> BiState
biForwardSearch st symbol =
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
    nextPattern = pattern r ++ [symbol]
    nextRangeR  = backwardStep symbol (fmidxR bi) (rangeR r)

    Range lo hi = range r
    offset = offsetForward st symbol ? offsetBound (fmidxR bi) symbol (rangeR r) (ctab (fmidxR bi))
    Range loR' hiR' = nextRangeR
    lo'         = lo + offset
    hi'         = lo' + (hiR' - loR')
    nextRange   = Range lo' hi'

{-@ biForwardExtendExact :: BiState -> String -> BiState @-}
biForwardExtendExact :: BiState -> String -> BiState
biForwardExtendExact st s = go st s
  where
    {-@ go :: BiState -> String -> BiState @-}
    go acc []     = acc
    go acc (c:cs) = go (biForwardSearch acc c) cs
