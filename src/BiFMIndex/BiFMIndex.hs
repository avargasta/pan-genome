{-@ LIQUID "--reflection"     @-}

module BiFMIndex.BiFMIndex where

import FMIndex.Tables (cTable, occTable, cLookup, occLookup)
import FMIndex.BWT    (buildBWT)
import FMIndex.Types ( FMIndex, bwt )
import FMIndex.FMIndex ( buildFMIndex )
import BiFMIndex.Types ( BiFMIndex(..), BiRange(..), BiState(..) )
import Data.ProofCombinators ((?))

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
    { origRange = (0, nFwd)
    , revRange  = (0, nBwd)
    , pattern   = ""
    }
  }
  where
    nFwd = length (bwt (orig bi))
    nBwd = length (bwt (rev bi))