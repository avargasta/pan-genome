{-@ LIQUID "--reflection"     @-}

module BiFMIndex.BiFMIndex where

import FMIndex.Types ( bwt, Range(..) )
import FMIndex.FMIndex ( buildFMIndex )
import BiFMIndex.Types ( BiFMIndex(..), BiRange(..), BiState(..) )

buildBiFMIndex :: String -> BiFMIndex
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
