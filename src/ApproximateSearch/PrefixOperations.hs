{-@ LIQUID "--reflection" @-}

module ApproximateSearch.PrefixOperations where

import BiFMIndex.Types (BiState(..))
import BiFMIndex.BiBackwardSearch (biBackwardStep)
import ApproximateSearch.Types (Coverage, isEmptyRange, rangeWidth, enumerateMismatches)

-- | Extend each match leftwards from @start - 1@ to @0@ using
--   'biBackwardStep': exact steps keep the interval, narrowed or empty
--   steps emit checkpoints from the state before the failed extension.
{-@ prefixExtension :: [(BiState, Coverage)] -> String -> [(BiState, Coverage)] @-}
prefixExtension :: [(BiState, Coverage)] -> String -> [(BiState, Coverage)]
prefixExtension states s = concatMap extendOne states
  where
    {-@ extendOne :: (BiState, Coverage) -> [(BiState, Coverage)] @-}
    extendOne :: (BiState, Coverage) -> [(BiState, Coverage)]
    extendOne (st, (start, end))
      | start < 0 || start > length s = []
      | otherwise                     = go st start end

    {-@ go :: BiState -> {v:Nat | v <= len s} -> Nat -> [(BiState, Coverage)] @-}
    go :: BiState -> Int -> Int -> [(BiState, Coverage)]
    go cur 0      end = [(cur, (0, end))]
    go cur curPos end
      | isEmptyRange (biRange candidate)          = [(cur, (curPos, end))]
      | rangeWidth (biRange candidate) < curWidth = (cur, (curPos, end)) : go candidate (curPos - 1) end
      | otherwise                                = go candidate (curPos - 1) end
      where
        c         = s !! (curPos - 1)
        candidate = biBackwardStep cur c
        curWidth  = rangeWidth (biRange cur)

-- | Try one mismatch immediately before @start@ by testing all symbols
--   other than the expected one and retaining only non-empty branches.
{-@ prefixMismatch :: [(BiState, Coverage)] -> String -> [(BiState, Coverage)] @-}
prefixMismatch :: [(BiState, Coverage)] -> String -> [(BiState, Coverage)]
prefixMismatch states s = concatMap mismatchOne states
  where

    {-@ mismatchOne :: (BiState, Coverage) -> [(BiState, Coverage)] @-}
    mismatchOne :: (BiState, Coverage) -> [(BiState, Coverage)]
    mismatchOne ( _ , (0, _)) = []
    mismatchOne (st, (start, end))
      | start > length s = []
      | otherwise        = mismatchAt st start end

    {-@ mismatchAt :: BiState -> {v:Nat | 0 < v && v <= len s} -> Nat -> [(BiState, Coverage)] @-}
    mismatchAt :: BiState -> Int -> Int -> [(BiState, Coverage)]
    mismatchAt st start end = tryAll (start - 1) (enumerateMismatches (biIndex st) correct)
      where
        correct = s !! (start - 1)

        {-@ tryAll :: Nat -> String -> [(BiState, Coverage)] @-}
        tryAll :: Int -> String -> [(BiState, Coverage)]
        tryAll _      []     = []
        tryAll newPos (e:es)
          | isEmptyRange (biRange candidate) = rest
          | otherwise                        = (candidate, (newPos, end)) : rest
          where
            candidate = biBackwardStep st e
            rest      = tryAll newPos es
