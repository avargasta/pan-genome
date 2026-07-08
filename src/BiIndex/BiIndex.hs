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

{-@ initializeBiRange :: bi:BiIndex -> {r:BiRange | fst (fwdRange r) <= snd (fwdRange r) && snd (fwdRange r) <= len (bwt (fwd bi)) && fst (bwdRange r) <= snd (bwdRange r) && snd (bwdRange r) <= len (bwt (bwd bi)) } @-}
initializeBiRange :: BiIndex -> BiRange
initializeBiRange bi = BiRange
  { fwdRange = (0, nFwd)
  , bwdRange = (0, nBwd)
  , pattern  = ""
  }
  where
    nFwd = length (bwt (fwd bi))
    nBwd = length (bwt (bwd bi))