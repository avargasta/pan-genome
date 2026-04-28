{-@ LIQUID "--reflection" @-}

module BiIndex.BiIndex where

import FMIndex.Tables (cTable, occTable, cLookup, occLookup)
import FMIndex.BWT    (buildBWT)
import FMIndex.Types ( FMIndex, bwt )
import FMIndex.FMIndex ( buildFMIndex )
import BiIndex.Types ( BiIndex(..), BiRange(..) )

buildBiIndex :: [Char] -> BiIndex
buildBiIndex t = BiIndex
  { fwd = buildFMIndex t
  , bwd = buildFMIndex (reverse t)
  }

{-@ initializeBiRange :: bi:BiIndex -> BiRange @-}
initializeBiRange :: BiIndex -> BiRange
initializeBiRange bi = BiRange
  { fwdRange = (0, n)
  , bwdRange = (0, n)
  , pattern  = ""
  }
  where
    n = length (bwt (fwd bi))