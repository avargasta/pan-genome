{-@ LIQUID "--reflection" @-}

module FMIndex.FMIndex where

import FMIndex.Types ( FMIndex(FMIndex) )
import FMIndex.Tables ( cTable, occTable )
import FMIndex.BWT (buildBWT, buildSA)

-- | Constructs bwt, ctab, occtab, sa, then the assumed `stepBound`/`partitionBound`
-- ghost fields, in that order.
{-@ buildFMIndex :: t:String -> {v:FMIndex | len (bwt v) == len t + 1} @-}
buildFMIndex :: String -> FMIndex
buildFMIndex t = FMIndex bwt ctab occtab suffix_array undefined undefined
  where
    bwt           = buildBWT t
    ctab          = cTable bwt
    occtab        = occTable bwt
    suffix_array  = buildSA t