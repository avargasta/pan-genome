{-@ LIQUID "--reflection" @-}

-- | Core type definitions for FM-Index
module FMIndex.Types where

import Data.RList
import FMIndex.Tables (cLookup, occLookup)

-- | FM-Index data structure
data FMIndex = FMIndex
  { bwt  :: [Char]              -- ^ Burrows-Wheeler Transform of the text
  , ctab :: [(Char, Int)]       -- ^ C table: cumulative character counts
  , occtab  :: [(Char, [Int])]  -- ^ Occurrence table: counts of characters up to each position
  , sa   :: [Int]               -- ^ Suffix Array: indices of sorted suffixes
  , inv  :: Char -> Int -> ()   -- ^ Invariant: ensures consistency of tables with BWT
  }

{-@ data FMIndex = FMIndex 
   { bwt  :: {v:[Char] | 1 <= len v }            
   , ctab :: [(Char, {v:Nat | v <= len bwt })]    
  , occtab  :: [(Char, {xs:SortedList Nat | len bwt + 1 == len xs})]
   , sa   :: [Nat]
   , inv  :: c:Char -> i:{Nat | i <= len bwt} -> {v:() | cLookup c ctab + occLookup c i occtab  <= len bwt} 
   } @-}

instance Show FMIndex where
  show fidx = "FMIndex { bwt = " ++ show (bwt fidx)
           ++ ", ctab = " ++ show (ctab fidx)
           ++ ", occtab = " ++ show (occtab fidx)
           ++ ", sa = " ++ show (sa fidx)
           ++ " }"