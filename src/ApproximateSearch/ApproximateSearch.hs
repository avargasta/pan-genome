{-@ LIQUID "--reflection" @-}

module ApproximateSearch.ApproximateSearch where

import Data.List (nub)
import FMIndex.Types (Range(..), sa)
import FMIndex.Search (locate)
import BiFMIndex.Types (BiFMIndex(..), BiRange(..), BiState(..))
import Data.ProofCombinators ((?))
import BiFMIndex.BiFMIndex (initializeBiState)
import BiFMIndex.BiBackwardSearch (biBackwardSearchExact)
import ApproximateSearch.Types (Coverage)
import ApproximateSearch.PrefixOperations (prefixExtension, prefixMismatch)
import ApproximateSearch.SuffixOperations (suffixExtension, suffixMismatch)
import ApproximateSearch.SeedPieces (seedPieces)

-- | Exhaust a left branch by exact extension, then spend one mismatch at
-- each remaining checkpoint while budget permits; every recursive step
-- consumes one unit of budget, so the search terminates.
{-@ searchLeft :: BiState -> Coverage -> budget:Nat -> s:String
               -> [(BiState, Coverage, Nat)] / [budget] @-}
searchLeft :: BiState -> Coverage -> Int -> String -> [(BiState, Coverage, Int)]
searchLeft st coverage budget s = concatMap step (map withBudget (prefixExtension [(st, coverage)] s))
  where
    {-@ withBudget :: (BiState, Coverage) -> (BiState, Coverage, {v:Nat | v == budget}) @-}
    withBudget :: (BiState, Coverage) -> (BiState, Coverage, Int)
    withBudget (st', coverage') = (st', coverage', budget)

    {-@ step :: (BiState, Coverage, {v:Nat | v == budget}) -> [(BiState, Coverage, Nat)] @-}
    step :: (BiState, Coverage, Int) -> [(BiState, Coverage, Int)]
    step (st', (0, end), b) = [(st', (0, end), b)]
    step (st', (start, end), b)
      | b <= 0    = []
      | otherwise =
          concatMap (\(st'', coverage'') -> searchLeft st'' coverage'' (b - 1) s)
                    (prefixMismatch [(st', (start, end))] s)

-- | Mirror image of 'searchLeft': exhaust the right side of a branch,
--   stopping checkpoints at @end == length s@ instead of @start == 0@.
{-@ searchRight :: BiState -> Coverage -> budget:Nat -> s:String
                -> [(BiState, Coverage, Nat)] / [budget] @-}
searchRight :: BiState -> Coverage -> Int -> String -> [(BiState, Coverage, Int)]
searchRight st coverage budget s = concatMap step (map withBudget (suffixExtension [(st, coverage)] s))
  where
    {-@ withBudget :: (BiState, Coverage) -> (BiState, Coverage, {v:Nat | v == budget}) @-}
    withBudget :: (BiState, Coverage) -> (BiState, Coverage, Int)
    withBudget (st', coverage') = (st', coverage', budget)

    {-@ step :: (BiState, Coverage, {v:Nat | v == budget}) -> [(BiState, Coverage, Nat)] @-}
    step :: (BiState, Coverage, Int) -> [(BiState, Coverage, Int)]
    step (st', (start, end), b)
      | end >= length s = [(st', (start, end), b)]
      | b <= 0           = []
      | otherwise        =
          concatMap (\(st'', coverage'') -> searchRight st'' coverage'' (b - 1) s)
                    (suffixMismatch [(st', (start, end))] s)

-- | Run one pigeonhole seed to completion: exhaust the left side of the
--   seed with the full mismatch budget, then whatever budget is left over
--   exhausts the right side.
{-@ searchSeed :: BiState -> p:String -> Nat -> (String, Coverage) -> [(BiState, Coverage, Nat)] @-}
searchSeed :: BiState -> String -> Int -> (String, Coverage) -> [(BiState, Coverage, Int)]
searchSeed initial p k (piece, (start, end)) = seedBranches
  where
    seedSt       = biBackwardSearchExact initial piece
    leftBranches = searchLeft seedSt (start, end) k p
    seedBranches = concatMap continueRight leftBranches
    continueRight (st, coverage', b) = searchRight st coverage' b p

-- | Positions in T of every occurrence of `p` within Hamming distance `k`,
--   found by pigeonhole-partitioning `p` into `k + 1` seeds, extending each
--   seed in both directions while spending mismatches out of its budget,
--   and deduplicating the positions collected across all seeds (an
--   occurrence that needs no mismatch at all is rediscovered by every
--   seed that covers it).
{-@ approximateSearch :: BiFMIndex -> String -> Nat -> [Int] @-}
approximateSearch :: BiFMIndex -> String -> Int -> [Int]
approximateSearch bi p k = nub (concatMap positionsOf finals)
  where
    initial = initializeBiState bi
    seeds   = seedPieces p (k + 1)
    finals  = filter isFullMatch (concatMap (searchSeed initial p k) seeds)

    isFullMatch :: (BiState, Coverage, Int) -> Bool
    isFullMatch (_, (start, end), _) = start == 0 && end == length p

    positionsOf :: (BiState, Coverage, Int) -> [Int]
    positionsOf (st, _, _)
      | l < h     = locate fidx l (h ? sa fidx)
      | otherwise = []
      where
        Range l h = range (biRange st)
        fidx      = fmidx (biIndex st)
