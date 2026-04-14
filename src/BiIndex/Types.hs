{-@ LIQUID "--reflection" @-}

module BiIndex.Types where

import FMIndex.Tables (cTable, occTable, cLookup, occLookup)
import FMIndex.BWT    (buildBWT)
import FMIndex.Types ( FMIndex )
import FMIndex.FMIndex ( buildFMIndex )

data BiIndex = BiIndex
  { fwd :: FMIndex
  , bwd :: FMIndex
  }

buildBiIndex :: [Char] -> BiIndex
buildBiIndex t = BiIndex
  { fwd = buildFMIndex t
  , bwd = buildFMIndex (reverse t)
  }