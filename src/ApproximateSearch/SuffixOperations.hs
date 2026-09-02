{-@ LIQUID "--reflection" @-}

module ApproximateSearch.SuffixOperations where

import BiFMIndex.Types (BiState(..))
import BiFMIndex.BiForwardSearch (biForwardStep)
import ApproximateSearch.Types (Coverage, isEmptyRange, rangeWidth, enumerateMismatches)

-- | Extend each match rightwards from @end@ to @length s@ using
--   'biForwardStep': exact steps keep the interval, narrowed or empty
--   steps emit checkpoints from the state before the failed extension.
{-@ suffixExtension :: [(BiState, Coverage)] -> String -> [(BiState, Coverage)] @-}
suffixExtension :: [(BiState, Coverage)] -> String -> [(BiState, Coverage)]
suffixExtension states s = concatMap extendOneR states
  where
    {-@ extendOneR :: (BiState, Coverage) -> [(BiState, Coverage)] @-}
    extendOneR :: (BiState, Coverage) -> [(BiState, Coverage)]
    extendOneR (st, (start, end))
      | end < 0 || end > length s = []
      | otherwise                 = goR st start end

    {-@ goR :: cur:BiState -> start:Nat -> end:{v:Nat | v <= len s} -> [(BiState, Coverage)] / [len s - end] @-}
    goR :: BiState -> Int -> Int -> [(BiState, Coverage)]
    goR cur start end
      | end == length s = [(cur, (start, end))]
      | otherwise =
          let c         = s !! end
              candidate = biForwardStep cur c
              curWidth  = rangeWidth (biRange cur)
          in if isEmptyRange (biRange candidate) then
               [(cur, (start, end))]
             else if rangeWidth (biRange candidate) < curWidth then
               (cur, (start, end)) : goR candidate start (end + 1)
             else
               goR candidate start (end + 1)

-- | Try one mismatch immediately after @end@ by testing all symbols
--   other than the expected one and retaining only non-empty branches.
{-@ suffixMismatch :: [(BiState, Coverage)] -> String -> [(BiState, Coverage)] @-}
suffixMismatch :: [(BiState, Coverage)] -> String -> [(BiState, Coverage)]
suffixMismatch states s = concatMap mismatchOneR states
  where
    {-@ mismatchOneR :: (BiState, Coverage) -> [(BiState, Coverage)] @-}
    mismatchOneR :: (BiState, Coverage) -> [(BiState, Coverage)]
    mismatchOneR (st, (start, end))
      | end >= length s = []
      | otherwise        = mismatchAtR st start end

    {-@ mismatchAtR :: BiState -> Nat -> {v:Nat | v < len s} -> [(BiState, Coverage)] @-}
    mismatchAtR :: BiState -> Int -> Int -> [(BiState, Coverage)]
    mismatchAtR st start end = tryAllR (end + 1) (enumerateMismatches (biIndex st) correct)
      where
        correct = s !! end

        {-@ tryAllR :: Nat -> String -> [(BiState, Coverage)] @-}
        tryAllR :: Int -> String -> [(BiState, Coverage)]
        tryAllR _      []     = []
        tryAllR newEnd (e:es)
          | isEmptyRange (biRange candidate) = rest
          | otherwise                        = (candidate, (start, newEnd)) : rest
          where
            candidate = biForwardStep st e
            rest      = tryAllR newEnd es
