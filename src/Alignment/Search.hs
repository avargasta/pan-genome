{-@ LIQUID "--reflection" @-}

module Alignment.Search where

import Data.List (nub)
import FMIndex.Types (Range(..), saLen)
import FMIndex.Search (locate)
import BiFMIndex.Types (BiFMIndex(..), BiRange(..), BiState(..))
import Data.ProofCombinators ((?))
import BiFMIndex.BiFMIndex (initializeBiState)
import BiFMIndex.BiBackwardSearch (biBackwardExtendExact)
import Alignment.BidirectionalSearch
  ( prefixExtension, prefixMismatch, suffixExtension, suffixMismatch )

-- ---------------------------------------------------------------------------
-- Seed partition
-- ---------------------------------------------------------------------------

-- | Split a pattern into `n` contiguous pieces covering it fully, as equal
--   in length as possible (the first `length p `mod` n` pieces get one
--   extra character). By the pigeonhole principle, an occurrence with at
--   most `n - 1` mismatches must match at least one piece exactly.
{-@ seedPieces :: p:String -> n:{Nat | 0 < n} -> [(String, (Nat, Nat))] @-}
seedPieces :: String -> Int -> [(String, (Int, Int))]
seedPieces p n = go 0 0
  where
    len   = length p
    base  = len `div` n
    extra = len `mod` n

    {-@ go :: i:{Nat | i <= n} -> Nat -> [(String, (Nat, Nat))] / [n - i] @-}
    go :: Int -> Int -> [(String, (Int, Int))]
    go i start
      | i >= n    = []
      | otherwise = (piece, (start, end)) : go (i + 1) end
      where
        pieceLen = base + (if i < extra then 1 else 0)
        end      = start + pieceLen
        piece    = take pieceLen (drop start p)

-- ---------------------------------------------------------------------------
-- searchLeft / searchRight
-- ---------------------------------------------------------------------------

-- | Exhaust the left side of a branch: extend exactly as far as possible
--   ('prefixExtension', which walks all the way down to every checkpoint in
--   one go, carrying the branch's mismatch budget through unchanged since
--   extending exactly never spends any of it), and at every checkpoint that
--   didn't reach @start == 0@, spend one mismatch -- if any budget remains
--   -- and keep going from there. Terminates because every recursive call
--   back into 'searchLeft' spends exactly one unit of @budget@ ('step'
--   carries the same measure).
{-@ searchLeft :: BiState -> (Nat, Nat) -> budget:Nat -> s:String
               -> [(BiState, (Nat, Nat), Nat)] / [budget] @-}
searchLeft :: BiState -> (Int, Int) -> Int -> String -> [(BiState, (Int, Int), Int)]
searchLeft st coverage budget s = concatMap step (map withBudget (prefixExtension [(st, coverage)] s))
  where
    {-@ withBudget :: (BiState, (Nat, Nat)) -> (BiState, (Nat, Nat), {v:Nat | v == budget}) @-}
    withBudget :: (BiState, (Int, Int)) -> (BiState, (Int, Int), Int)
    withBudget (st', coverage') = (st', coverage', budget)

    {-@ step :: (BiState, (Nat, Nat), {v:Nat | v == budget}) -> [(BiState, (Nat, Nat), Nat)] @-}
    step :: (BiState, (Int, Int), Int) -> [(BiState, (Int, Int), Int)]
    step (st', (0, end), b) = [(st', (0, end), b)]
    step (st', (start, end), b)
      | b <= 0    = []
      | otherwise =
          concatMap (\(st'', coverage'') -> searchLeft st'' coverage'' (b - 1) s)
                    (prefixMismatch [(st', (start, end))] s)

-- | Mirror image of 'searchLeft': exhaust the right side of a branch,
--   stopping checkpoints at @end == length s@ instead of @start == 0@.
{-@ searchRight :: BiState -> (Nat, Nat) -> budget:Nat -> s:String
                -> [(BiState, (Nat, Nat), Nat)] / [budget] @-}
searchRight :: BiState -> (Int, Int) -> Int -> String -> [(BiState, (Int, Int), Int)]
searchRight st coverage budget s = concatMap step (map withBudget (suffixExtension [(st, coverage)] s))
  where
    {-@ withBudget :: (BiState, (Nat, Nat)) -> (BiState, (Nat, Nat), {v:Nat | v == budget}) @-}
    withBudget :: (BiState, (Int, Int)) -> (BiState, (Int, Int), Int)
    withBudget (st', coverage') = (st', coverage', budget)

    {-@ step :: (BiState, (Nat, Nat), {v:Nat | v == budget}) -> [(BiState, (Nat, Nat), Nat)] @-}
    step :: (BiState, (Int, Int), Int) -> [(BiState, (Int, Int), Int)]
    step (st', (start, end), b)
      | end >= length s = [(st', (start, end), b)]
      | b <= 0           = []
      | otherwise        =
          concatMap (\(st'', coverage'') -> searchRight st'' coverage'' (b - 1) s)
                    (suffixMismatch [(st', (start, end))] s)

-- ---------------------------------------------------------------------------
-- Per-seed search and the top-level driver
-- ---------------------------------------------------------------------------

-- | Run one pigeonhole seed to completion: exhaust the left side of the
--   seed with the full mismatch budget, then whatever budget is left over
--   exhausts the right side.
{-@ searchSeed :: BiState -> p:String -> Nat -> (String, (Nat, Nat)) -> [(BiState, (Nat, Nat), Nat)] @-}
searchSeed :: BiState -> String -> Int -> (String, (Int, Int)) -> [(BiState, (Int, Int), Int)]
searchSeed initial p k (piece, (start, end)) = seedBranches
  where
    seedSt       = biBackwardExtendExact initial piece
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

    isFullMatch :: (BiState, (Int, Int), Int) -> Bool
    isFullMatch (_, (start, end), _) = start == 0 && end == length p

    positionsOf :: (BiState, (Int, Int), Int) -> [Int]
    positionsOf (st, _, _)
      | l < h     = locate fidx l (h ? saLen fidx)
      | otherwise = []
      where
        Range l h = range (biRange st)
        fidx      = fmidx (biIndex st)
