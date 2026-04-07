{-@ LIQUID "--reflection" @-}

-- | Core type definitions for FM-Index
module FMIndex.Types where

import FMIndex.Tables
import FMIndex.BWT (buildBWT)
import Data.RList 

-- | FM-Index data structure
data FMIndex = FMIndex
  { bwt  :: [Char]              -- ^ Burrows-Wheeler Transform of the text
  , ctab :: [(Char, Int)]       -- ^ C table: cumulative character counts
  , occtab  :: [(Char, [Int])]     -- ^ Occurrence table: counts of characters up to each position
  , inv  :: Char -> Int -> ()   -- ^ Invariant: ensures consistency of tables with BWT
  }

{-@ data FMIndex = FMIndex 
   { bwt  :: {v:[Char] | 1 <= len v }            
   , ctab :: [(Char, {v:Nat | v <= len bwt })]    
   , occtab  :: [(Char, {xs:SortedList Nat | len bwt + 1 == len xs })] 
   , inv  :: c:Char -> i:{Nat | i <= len bwt} -> {v:() | cLookup c ctab + occLookup c i occtab  <= len bwt} 
   } @-}


buildFMIndex :: [Char] -> FMIndex
buildFMIndex t = FMIndex bwt ctab occtab undefined
  where
    bwt    = buildBWT t
    ctab   = cTable bwt
    occtab = occTable bwt

