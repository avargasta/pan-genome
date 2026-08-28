{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module BiFMIndex.BiBackwardSearch where

import FMIndex.Search (backwardStep)
import FMIndex.Types (FMIndex, bwt, ctab, occtab, offsetBound, Range(..))
import FMIndex.Tables (occLookup, offsetTable)
import BiFMIndex.Types (BiFMIndex(..), BiRange(..), BiState(..))
import Data.ProofCombinators ((?))

-- | Bidirectional BWT partition theorem (Lam et al. 2009): the occurrences
-- of `symbol`, together with everything smaller than it, within the
-- current original range, never exceed that range's width. Made checkable
-- by injecting the fact from the original index's own 'offsetBound' ghost
-- field -- pinned to 'offsetTable', the very traversal computed below, so
-- the assumption can't be misapplied to a value the algorithm didn't
-- actually produce.
{-@ reflect offsetBackward @-}
{-@ offsetBackward :: st:BiState -> symbol:Char -> Nat @-}
offsetBackward :: BiState -> Char -> Int
offsetBackward st symbol = offsetTable symbol (lo rng) (hi rng) (ctab fi) (occtab fi)
  where
    rng = origRange (range st)
    fi  = orig (index st)

-- | Extend the current pattern with one symbol.
{-@ biBackwardSearch :: BiState -> Char -> BiState @-}
biBackwardSearch :: BiState -> Char -> BiState
biBackwardSearch st symbol =
  BiState
    { index = bi
    , range = BiRange
        { pattern   = nextPattern
        , origRange = nextOrigRange
        , revRange  = nextRevRange
        }
    }
  where
    bi            = index st
    r             = range st
    nextPattern   = [symbol] ++ pattern r
    nextOrigRange = backwardStep symbol (orig bi) (origRange r)

    rLo    = lo (revRange r)
    rHi    = hi (revRange r)
    offset = offsetBackward st symbol ? offsetBound (orig bi) symbol (origRange r) (ctab (orig bi))
    noLo   = lo nextOrigRange
    noHi   = hi nextOrigRange
    nrLo          = rLo + offset
    nrHi          = nrLo + (noHi - noLo)
    nextRevRange  = Range nrLo nrHi

{-@ biBackwardExtendExact :: BiState -> String -> BiState @-}
biBackwardExtendExact :: BiState -> String -> BiState
biBackwardExtendExact st s = go st (reverse s)
  where
    {-@ go :: BiState -> String -> BiState @-}
    go acc []     = acc
    go acc (c:cs) = go (biBackwardSearch acc c) cs
