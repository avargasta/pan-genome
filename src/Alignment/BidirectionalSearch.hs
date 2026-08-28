{-@ LIQUID "--reflection" @-}

module Alignment.BidirectionalSearch where

import BiFMIndex.Types (BiFMIndex(..), BiRange(..), BiState(..))
import BiFMIndex.BiBackwardSearch (biBackwardSearch)
import BiFMIndex.BiForwardSearch (biForwardSearch)
import FMIndex.Types (ctab, Range(..))

-- Me gustaría tener:
-- Extend prefix ranges from the last character of String down to the first character, filtering empty ranges.
-- prefixExtension :: [(BiState, Int)] -> String -> [(BiState, Int)]

-- Extend by one mismatch character
-- prefixMismatch :: [(BiState, Int)] -> String -> [(BiState, Int)]


-- La idea es que el Int sea la posición del pattern en el que efectivamente estoy o he hecho el mismatch.
-- La String es la subcadena de pattern que en cada caso estaré byscando.

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

-- | A range is empty when its lower bound is not strictly below its upper
--   bound (no occurrences left).
isEmptyRange :: BiRange -> Bool
isEmptyRange r = rangeWidth r <= 0

-- | Number of occurrences currently covered by a range.
rangeWidth :: BiRange -> Int
rangeWidth r = hi (range r) - lo (range r)

-- | All alphabet characters that differ from the given one (and from the
--   sentinel '$'). These are the candidate substitutions at a mismatch.
enumerateMismatches :: BiFMIndex -> Char -> [Char]
enumerateMismatches bi c = filter (\x -> x /= c && x /= '$') (map fst (ctab (fmidx bi)))

-- ---------------------------------------------------------------------------
-- prefixExtension
-- ---------------------------------------------------------------------------

-- | Extend every (state, (start, end)) entry one character at a time,
--   walking pattern positions @start - 1@ down to @0@ -- exactly the order
--   'biBackwardSearch' needs, since it grows the pattern to the left. Only
--   @start@ drives the walk; @end@ is carried through untouched and simply
--   identifies the position of the pattern where this entry's match ends.
--   Extending is "free" (no checkpoint) as long as the range keeps the same
--   width. The moment adding the next character would either narrow the
--   range (some of the occurrences matched so far stop matching -- a good
--   spot to later try a mismatch there) or empty it out entirely, the state
--   *before* that character is emitted as a checkpoint; narrowing keeps
--   going with the smaller range afterwards, emptying stops the walk right
--   there. Running out of characters (start == 0) also emits the state
--   reached so far -- in particular, an entry that's already at start 0
--   just gets handed back unchanged.
--
--   The substring is indexed absolutely (its index 0 is the pattern's index
--   0), so entries at different positions can share the same call: each one
--   only ever looks at @s !! (start - 1)@, @s !! (start - 2)@, ... down to
--   @s !! 0@.
{-@ prefixExtension :: [(BiState, (Nat, Nat))] -> String -> [(BiState, (Nat, Nat))] @-}
prefixExtension :: [(BiState, (Int, Int))] -> String -> [(BiState, (Int, Int))]
prefixExtension states s = concatMap extendOne states
  where
    {-@ extendOne :: (BiState, (Nat, Nat)) -> [(BiState, (Nat, Nat))] @-}
    extendOne :: (BiState, (Int, Int)) -> [(BiState, (Int, Int))]
    extendOne (st, (start, end))
      | start < 0 || start > length s = []
      | otherwise                     = go st start end

    {-@ go :: BiState -> {v:Nat | v <= len s} -> Nat -> [(BiState, (Nat, Nat))] @-}
    go :: BiState -> Int -> Int -> [(BiState, (Int, Int))]
    go cur 0      end = [(cur, (0, end))]
    go cur curPos end
      | isEmptyRange (biRange candidate)          = [(cur, (curPos, end))]
      | rangeWidth (biRange candidate) < curWidth = (cur, (curPos, end)) : go candidate (curPos - 1) end
      | otherwise                                = go candidate (curPos - 1) end
      where
        c         = s !! (curPos - 1)
        candidate = biBackwardSearch cur c
        curWidth  = rangeWidth (biRange cur)

-- ---------------------------------------------------------------------------
-- prefixMismatch
-- ---------------------------------------------------------------------------

-- | For each (state, (start, end)) entry, introduce a single mismatch at
--   the position right before @start@: try every alphabet symbol other than
--   the one that actually occurs there, keeping only the resulting
--   non-empty states. @end@ is only ever carried through unchanged, never
--   read.
--
--   The substring is indexed absolutely (its index 0 is the pattern's index
--   0), so entries at different positions can share the same call: the
--   correct character to avoid for a given (state, start) is
--   @s !! (start - 1)@, not simply the last character of s.
{-@ prefixMismatch :: [(BiState, (Nat, Nat))] -> String -> [(BiState, (Nat, Nat))] @-}
prefixMismatch :: [(BiState, (Int, Int))] -> String -> [(BiState, (Int, Int))]
prefixMismatch states s = concatMap mismatchOne states
  where

    {-@ mismatchOne :: (BiState, (Nat, Nat)) -> [(BiState, (Nat, Nat))] @-}
    mismatchOne :: (BiState, (Int, Int)) -> [(BiState, (Int, Int))]
    mismatchOne ( _ , (0, _)) = []
    mismatchOne (st, (start, end))
      | start > length s = []
      | otherwise        = mismatchAt st start end

    {-@ mismatchAt :: BiState -> {v:Nat | 0 < v && v <= len s} -> Nat -> [(BiState, (Nat, Nat))] @-}
    mismatchAt :: BiState -> Int -> Int -> [(BiState, (Int, Int))]
    mismatchAt st start end = tryAll (start - 1) (enumerateMismatches (biIndex st) correct)
      where
        correct = s !! (start - 1)

        {-@ tryAll :: Nat -> [Char] -> [(BiState, (Nat, Nat))] @-}
        tryAll :: Int -> [Char] -> [(BiState, (Int, Int))]
        tryAll _      []     = []
        tryAll newPos (e:es)
          | isEmptyRange (biRange candidate) = rest
          | otherwise                        = (candidate, (newPos, end)) : rest
          where
            candidate = biBackwardSearch st e
            rest      = tryAll newPos es

-- ---------------------------------------------------------------------------
-- suffixExtension
-- ---------------------------------------------------------------------------

-- | Mirror image of 'prefixExtension': extend every (state, (start, end))
--   entry one character at a time, walking pattern positions @end@ up to
--   @length s - 1@ -- the order 'biForwardSearch' needs, since it grows the
--   pattern to the right. Only @end@ drives the walk; @start@ is carried
--   through untouched and simply identifies the position of the pattern
--   where this entry's match begins. Extending is "free" (no checkpoint) as
--   long as the range keeps the same width. The moment adding the next
--   character would either narrow the range (a good spot to later try a
--   mismatch there) or empty it out entirely, the state *before* that
--   character is emitted as a checkpoint; narrowing keeps going with the
--   smaller range afterwards, emptying stops the walk right there. Running
--   out of characters (end == length s) also emits the state reached so far
--   -- in particular, an entry already at the end of s just gets handed
--   back unchanged.
--
--   The substring is indexed absolutely (its index 0 is the pattern's index
--   0), so entries at different positions can share the same call: each one
--   only ever looks at @s !! end@, @s !! (end + 1)@, ... up to
--   @s !! (length s - 1)@.
{-@ suffixExtension :: [(BiState, (Nat, Nat))] -> String -> [(BiState, (Nat, Nat))] @-}
suffixExtension :: [(BiState, (Int, Int))] -> String -> [(BiState, (Int, Int))]
suffixExtension states s = concatMap extendOneR states
  where
    {-@ extendOneR :: (BiState, (Nat, Nat)) -> [(BiState, (Nat, Nat))] @-}
    extendOneR :: (BiState, (Int, Int)) -> [(BiState, (Int, Int))]
    extendOneR (st, (start, end))
      | end < 0 || end > length s = []
      | otherwise                 = goR st start end

    {-@ goR :: cur:BiState -> start:Nat -> end:{v:Nat | v <= len s} -> [(BiState, (Nat, Nat))] / [len s - end] @-}
    goR :: BiState -> Int -> Int -> [(BiState, (Int, Int))]
    goR cur start end
      | end == length s = [(cur, (start, end))]
      | otherwise =
          let c         = s !! end
              candidate = biForwardSearch cur c
              curWidth  = rangeWidth (biRange cur)
          in if isEmptyRange (biRange candidate) then
               [(cur, (start, end))]
             else if rangeWidth (biRange candidate) < curWidth then
               (cur, (start, end)) : goR candidate start (end + 1)
             else
               goR candidate start (end + 1)

-- ---------------------------------------------------------------------------
-- suffixMismatch
-- ---------------------------------------------------------------------------

-- | Mirror image of 'prefixMismatch': for each (state, (start, end)) entry,
--   introduce a single mismatch at the position right at @end@: try every
--   alphabet symbol other than the one that actually occurs there, keeping
--   only the resulting non-empty states. @start@ is only ever carried
--   through unchanged, never read.
--
--   The substring is indexed absolutely (its index 0 is the pattern's index
--   0), so entries at different positions can share the same call: the
--   correct character to avoid for a given (state, end) is @s !! end@, not
--   simply the first character of s.
{-@ suffixMismatch :: [(BiState, (Nat, Nat))] -> String -> [(BiState, (Nat, Nat))] @-}
suffixMismatch :: [(BiState, (Int, Int))] -> String -> [(BiState, (Int, Int))]
suffixMismatch states s = concatMap mismatchOneR states
  where
    {-@ mismatchOneR :: (BiState, (Nat, Nat)) -> [(BiState, (Nat, Nat))] @-}
    mismatchOneR :: (BiState, (Int, Int)) -> [(BiState, (Int, Int))]
    mismatchOneR (st, (start, end))
      | end >= length s = []
      | otherwise        = mismatchAtR st start end

    {-@ mismatchAtR :: BiState -> Nat -> {v:Nat | v < len s} -> [(BiState, (Nat, Nat))] @-}
    mismatchAtR :: BiState -> Int -> Int -> [(BiState, (Int, Int))]
    mismatchAtR st start end = tryAllR (end + 1) (enumerateMismatches (biIndex st) correct)
      where
        correct = s !! end

        {-@ tryAllR :: Nat -> [Char] -> [(BiState, (Nat, Nat))] @-}
        tryAllR :: Int -> [Char] -> [(BiState, (Int, Int))]
        tryAllR _      []     = []
        tryAllR newEnd (e:es)
          | isEmptyRange (biRange candidate) = rest
          | otherwise                        = (candidate, (start, newEnd)) : rest
          where
            candidate = biForwardSearch st e
            rest      = tryAllR newEnd es
