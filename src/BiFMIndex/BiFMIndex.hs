{-@ LIQUID "--reflection"     @-}

module BiFMIndex.BiFMIndex where

import FMIndex.Tables (cTable, occTable, cLookup, occLookup)
import FMIndex.BWT    (buildBWT)
import FMIndex.Types ( FMIndex, bwt, Range(..) )
import FMIndex.FMIndex ( buildFMIndex )
import BiFMIndex.Types ( BiFMIndex(..), BiRange(..), BiState(..) )

buildBiFMIndex :: [Char] -> BiFMIndex
buildBiFMIndex t = BiFMIndex
  { orig = buildFMIndex t
  , rev = buildFMIndex (reverse t)
  }

{-@ initializeBiState :: bi:BiFMIndex -> BiState @-}
initializeBiState :: BiFMIndex -> BiState
initializeBiState bi = BiState
  { index = bi
  , range = BiRange
    { origRange = Range 0 nFwd
    , revRange  = Range 0 nBwd
    , pattern   = ""
    }
  }
  where
    nFwd = length (bwt (orig bi))
    nBwd = length (bwt (rev bi))