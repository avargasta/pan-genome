{-@ LIQUID "--reflection" @-}

module Alignment.BidirectionalSearch where

import BiIndex.Types            (BiIndex(..), BiRange(..))
import BiIndex.BiIndex          (initializeBiRange)
import BiIndex.BiBackwardSearch (biBackwardSearch, biBackwardExtendExact)
import BiIndex.BiForwardSearch  (biForwardSearch, biForwardExtendExact)
import FMIndex.Types            (ctab, bwt)

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

-- | All characters in the index alphabet that differ from the given character.
--   These are the candidate substitutions at a mismatch position.
enumerateMismatches :: BiIndex -> Char -> [Char]
enumerateMismatches bi c = filter (\x -> x /= c && x /= '$') (map fst (ctab (fwd bi)))

-- | Backward-search over p[start..end] (inclusive) extending from an initial range.
{-@ biBackwardSearchSegment :: bi:BiIndex
                         -> p:[Char]
       -> start:{v:Nat | v < len p}
       -> end:{v:Nat | start <= v && v < len p}
                         -> range:{r:BiRange | fst (fwdRange r) <= snd (fwdRange r)
                                                 && snd (fwdRange r) <= len (bwt (fwd bi))
                                                 && fst (bwdRange r) <= snd (bwdRange r)}
                         -> BiRange @-}
biBackwardSearchSegment :: BiIndex -> [Char] -> Int -> Int -> BiRange -> BiRange
biBackwardSearchSegment bi p start end range =
        biBackwardExtendExact bi range segment
    where
  segment = take (end - start + 1) (drop start p)

-- | Forward-search over p[start..end] (inclusive) extending from an initial range.
{-@ biForwardSearchSegment :: bi:BiIndex
                         -> p:[Char]
                         -> start:{v:Nat | v < len p}
                         -> end:{v:Nat | start <= v && v < len p}
                         -> range:{r:BiRange | fst (fwdRange r) <= snd (fwdRange r)
                                                 && fst (bwdRange r) <= snd (bwdRange r)
                                                 && snd (bwdRange r) <= len (bwt (bwd bi))}
                         -> BiRange @-}
biForwardSearchSegment :: BiIndex -> [Char] -> Int -> Int -> BiRange -> BiRange
biForwardSearchSegment bi p start end range =
        biForwardExtendExact bi range segment
    where
        segment = take (end - start + 1) (drop start p)

-- -- | For each position j (end down to start), pair j with the range that covers
-- --   P[j+1..m] exactly.
{-@ exactPrefixRanges :: bi:BiIndex
                        -> p:[Char]
                        -> start:{v:Nat | 0 < v && v < len p}
                        -> end:{v:Nat | start <= v && v < len p}
                        -> range:{r:BiRange | fst (fwdRange r) <= snd (fwdRange r)
                                            && snd (fwdRange r) <= len (bwt (fwd bi))
                                            && fst (bwdRange r) <= snd (bwdRange r)}
                        -> [(Int, BiRange)] @-}
exactPrefixRanges :: BiIndex -> [Char] -> Int -> Int -> BiRange -> [(Int, BiRange)]
exactPrefixRanges bi p start end range = go (end - 1) (biBackwardSearch bi range (p !! (end - 1)))
  where
    {-@ go :: j:{v:Nat | v <= end}
           -> subrange:{r:BiRange | fst (fwdRange r) <= snd (fwdRange r)
                                 && snd (fwdRange r) <= len (bwt (fwd bi))
                                 && fst (bwdRange r) <= snd (bwdRange r)}
           -> [(Int, BiRange)] @-}
    -- j    : current 1-indexed position (counts down to start)
    -- range: covers P[j+1..m] exactly
    go j subrange
      | j < start     = []
      | otherwise = (j, subrange) : go (j - 1) (biBackwardSearch bi subrange (p !! (j - 1)))

-- | For each position i (start up to end), pair i with the range that covers
-- | P[1..i-1] exactly.
{-@ exactSuffixRanges :: bi:BiIndex
                        -> p:[Char]
                        -> start:{v:Nat | 0 < v && v < len p}
                        -> end:{v:Nat | start <= v && v < len p}
                        -> range:{r:BiRange | fst (fwdRange r) <= snd (fwdRange r)
                                            && fst (bwdRange r) <= snd (bwdRange r)
                                            && snd (bwdRange r) <= len (bwt (bwd bi))}
                        -> [(Int, BiRange)] @-}
exactSuffixRanges :: BiIndex -> [Char] -> Int -> Int -> BiRange -> [(Int, BiRange)]
exactSuffixRanges bi p start end range = go steps start range
  where
    steps = end - start + 1

    {-@ go :: fuel:Nat
           -> i:{v:Nat | start <= v && v <= end + 1 && v + fuel == end + 1}
           -> subrange:{r:BiRange | fst (fwdRange r) <= snd (fwdRange r)
                                 && fst (bwdRange r) <= snd (bwdRange r)
                                 && snd (bwdRange r) <= len (bwt (bwd bi))}
           -> [(Int, BiRange)] @-}
    go :: Int -> Int -> BiRange -> [(Int, BiRange)]
    -- i    : current 1-indexed position (counts up to end)
    -- range: covers P[1..i-1] exactly
    go fuel i subrange
      | fuel == 0  = []
      | otherwise  = (i, subrange) : go (fuel - 1) (i + 1) (biForwardSearch bi subrange (p !! (i - 1)))



-- | Discard empty ranges (lo >= hi means no occurrences).
nonEmpty :: BiRange -> [BiRange] -- ----> MAKE IT BOOLEAN 
nonEmpty r@(BiRange (lo, hi) _ _) = if lo < hi then [r] else []

-- | For each candidate (j, rangeJ), try every mismatch substitution at position j-1.
--   Returns (j-1, substitution, resulting range) for non-empty results.
{-@ ignore tryMismatch @-}
tryMismatch :: BiIndex -> [Char] -> [(Int, BiRange)] -> [(Int, Char, BiRange)]
tryMismatch bi p candidates =
  [ (j - 1, e, r)
  | (j, rangeJ) <- candidates
  , e <- enumerateMismatches bi (p !! (j - 1))
  , let r = biBackwardSearch bi rangeJ e
  , _ <- nonEmpty r
  ]

-- | Extend prefix ranges from end-1 down to start, filtering empty ranges.
--   When end == start == 0, returns the seed range at position 0 (if non-empty).
{-@ ignore prefixExtension @-}
prefixExtension :: BiIndex -> [Char] -> Int -> Int -> BiRange -> [(Int, BiRange)]
prefixExtension bi p start end range
  | end == 0 && start == 0 = [(0, range) | _ <- nonEmpty range]
  | end <= start           = []
  | otherwise              = go (end - 1) (biBackwardSearch bi range (p !! (end - 1)))
  where
    go j subrange
      | j < start = []
      | otherwise = [ (j, subrange) | _ <- nonEmpty subrange ]
                 ++ go (j - 1) (biBackwardSearch bi subrange (p !! (j - 1)))

-- ---------------------------------------------------------------------------
-- Case A
-- ---------------------------------------------------------------------------

-- | Case A: both mismatches e1 < e2 lie within P[1..s2] (the first two parts).
--
--   Split points (1-indexed):
--     s1 – end of part 1  (P1 = P[1..s1], not used in this case)
--     s2 – end of part 2  (P2 = P[s1+1..s2], P3 = P[s2+1..m])
--
--   Returns all BiRanges with exactly 2 mismatches, both located in P[1..s2].
--   Executable step-by-step walkthrough and a concrete `caseA` implementation
--   are now in app/Main.hs.
