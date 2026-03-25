{-@ LIQUID "--reflection" @-}

-- | Core type definitions for FM-Index
module FMIndex.Types where

import FMIndex.Tables 
import Data.RList 

-- | FM-Index data structure
data FMIndex = FMIndex
  { bwt  :: [Char]              -- ^ Burrows-Wheeler Transform of the text
  , ctab :: [(Char, Int)]       -- ^ C table: cumulative character counts
  , occ  :: [(Char, [Int])]     -- ^ Occurrence table: counts of characters up to each position
  , inv  :: Char -> Int -> ()   -- ^ Invariant: ensures consistency of tables with BWT
  }

{-@ data FMIndex = FMIndex 
   { bwt  :: {v:[Char] | 1 <= len v }            
   , ctab :: [(Char, {v:Nat | v <= len bwt })]    
   , occ  :: [(Char, {xs:SortedList Nat | len bwt + 1 == len xs })] 
   , inv  :: c:Char -> i:{Nat | i <= len bwt} -> {v:() | cLookup c ctab + occLookup c i occ  <= len bwt} 
   } @-}


