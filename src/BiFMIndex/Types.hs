{-@ LIQUID "--reflection" @-}

module BiFMIndex.Types where

import FMIndex.Types ( FMIndex, bwt, Range(..) )

data BiRange = BiRange
  { range   :: Range
  , rangeR  :: Range
  , pattern :: String
  }

{-@ data BiRange = BiRange
  { range   :: Range
  , rangeR  :: Range
  , pattern :: String
  } @-}

data BiFMIndex = BiFMIndex
  { fmidx  :: FMIndex
  , fmidxR :: FMIndex
  }

{-@ data BiFMIndex = BiFMIndex
  { fmidx  :: FMIndex
  , fmidxR :: {v:FMIndex | len (bwt v) == len (bwt fmidx)}
  } @-}

data BiState = BiState
  { biIndex :: BiFMIndex
  , biRange :: BiRange
  }

-- "lo <= hi" for each range is already guaranteed by the Range type itself;
-- only the BWT bound and the size-coupling invariant need to be stated here.
{-@ data BiState = BiState
  { biIndex :: BiFMIndex
  , biRange :: {r:BiRange | hi (range r) <= len (bwt (fmidx biIndex))
                          && hi (rangeR r)  <= len (bwt (fmidxR biIndex))
                          && hi (range r) - lo (range r) == hi (rangeR r) - lo (rangeR r) }
  } @-}

--------------------------------------------------------------------------

instance Show BiFMIndex where
  show bi = "BiFMIndex { fmidx = " ++ show (fmidx bi)
           ++ ", fmidxR = " ++ show (fmidxR bi)
           ++ " }"

instance Show BiRange where
  show r = "BiRange { range = " ++ show (range r)
           ++ ", rangeR = " ++ show (rangeR r)
           ++ ", pattern = " ++ show (pattern r)
           ++ " }"

instance Show BiState where
  show st = "BiState { biIndex = " ++ show (biIndex st)
           ++ ", biRange = " ++ show (biRange st)
           ++ " }"
