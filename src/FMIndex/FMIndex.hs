{-@ LIQUID "--reflection" @-}

module FMIndex.FMIndex where

import FMIndex.Types ( FMIndex(FMIndex) )  
import FMIndex.Tables ( cTable, occTable )
import FMIndex.BWT (buildBWT, buildSA)
import Data.RList

buildFMIndex :: [Char] -> FMIndex
buildFMIndex t = FMIndex bwt ctab occtab suffix_array undefined
  where
    bwt           = buildBWT t
    ctab          = cTable bwt
    occtab        = occTable bwt
    suffix_array  = buildSA t