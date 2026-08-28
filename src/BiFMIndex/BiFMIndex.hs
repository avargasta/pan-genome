{-@ LIQUID "--reflection"     @-}

module BiFMIndex.BiFMIndex where

import FMIndex.Tables (cTable, occTable, cLookup, occLookup)
import FMIndex.BWT    (buildBWT)
import FMIndex.Types ( FMIndex, bwt, Range(..) )
import FMIndex.FMIndex ( buildFMIndex )
import BiFMIndex.Types ( BiFMIndex(..), BiRange(..), BiState(..) )

buildBiFMIndex :: [Char] -> BiFMIndex
buildBiFMIndex t = BiFMIndex
  { fmidx  = buildFMIndex t
  , fmidxR = buildFMIndex (reverse t)
  }

{-@ initializeBiState :: bi:BiFMIndex -> BiState @-}
initializeBiState :: BiFMIndex -> BiState
initializeBiState bi = BiState
  { biIndex = bi
  , biRange = BiRange
    { range   = Range 0 nFwd
    , rangeR  = Range 0 nBwd
    , pattern = ""
    }
  }
  where
    nFwd = length (bwt (fmidx bi))
    nBwd = length (bwt (fmidxR bi))
