{-@ LIQUID "--reflection" @-}

module Alignment.BidirectionalSearch where

import BiFMIndex.Types (BiFMIndex(..), BiRange(..), BiState(..))
import BiFMIndex.BiBackwardSearch (biBackwardSearch)
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
rangeWidth r = hi (origRange r) - lo (origRange r)

-- | All alphabet characters that differ from the given one (and from the
--   sentinel '$'). These are the candidate substitutions at a mismatch.
enumerateMismatches :: BiFMIndex -> Char -> [Char]
enumerateMismatches bi c = filter (\x -> x /= c && x /= '$') (map fst (ctab (orig bi)))

-- ---------------------------------------------------------------------------
-- prefixExtension
-- ---------------------------------------------------------------------------

-- | Extend every (state, pos) pair one character at a time, walking pattern
--   positions @pos - 1@ down to @0@ -- exactly the order 'biBackwardSearch'
--   needs, since it grows the pattern to the left. Extending is "free" (no
--   checkpoint) as long as the range keeps the same width. The moment adding
--   the next character would either narrow the range (some of the
--   occurrences matched so far stop matching -- a good spot to later try a
--   mismatch there) or empty it out entirely, the state *before* that
--   character is emitted as a checkpoint; narrowing keeps going with the
--   smaller range afterwards, emptying stops the walk right there. Running
--   out of characters (pos == 0) also emits the state reached so far -- in
--   particular, an entry that's already at position 0 just gets handed back
--   unchanged.
--
--   The substring is indexed absolutely (its index 0 is the pattern's index
--   0), so entries at different positions can share the same call: each one
--   only ever looks at @s !! (pos - 1)@, @s !! (pos - 2)@, ... down to
--   @s !! 0@.
{-@ ignore prefixExtension @-}
prefixExtension :: [(BiState, Int)] -> String -> [(BiState, Int)]
prefixExtension states s = concatMap extendOne states
  where
    extendOne :: (BiState, Int) -> [(BiState, Int)]
    extendOne (st, pos)
      | pos < 0 || pos > length s = []
      | otherwise                 = go (reverse (take pos s)) st pos

    go :: String -> BiState -> Int -> [(BiState, Int)]
    go []     cur curPos = [(cur, curPos)]
    go (c:cs) cur curPos
      | isEmptyRange (range candidate)          = [(cur, curPos)]
      | rangeWidth (range candidate) < curWidth = (cur, curPos) : go cs candidate (curPos - 1)
      | otherwise                                = go cs candidate (curPos - 1)
      where
        candidate = biBackwardSearch cur c
        curWidth  = rangeWidth (range cur)

-- ---------------------------------------------------------------------------
-- prefixMismatch
-- ---------------------------------------------------------------------------

-- | For each (state, pos) pair, introduce a single mismatch at the position
--   right before it: try every alphabet symbol other than the one that
--   actually occurs there, keeping only the resulting non-empty states.
--
--   The substring is indexed absolutely (its index 0 is the pattern's index
--   0), so entries at different positions can share the same call: the
--   correct character to avoid for a given (state, pos) is @s !! (pos - 1)@,
--   not simply the last character of s.
{-@ ignore prefixMismatch @-}
prefixMismatch :: [(BiState, Int)] -> String -> [(BiState, Int)]
prefixMismatch states s = concatMap mismatchOne states
  where
    mismatchOne :: (BiState, Int) -> [(BiState, Int)]
    mismatchOne (st, pos)
      | pos <= 0 || pos > length s = []
      | otherwise =
          [ (st', pos - 1)
          | e <- enumerateMismatches (index st) correct
          , let st' = biBackwardSearch st e
          , not (isEmptyRange (range st'))
          ]
      where
        correct = s !! (pos - 1)
