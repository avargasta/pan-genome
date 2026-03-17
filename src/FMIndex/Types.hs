-- | Core type definitions for FM-Index
module FMIndex.Types where

-- | FM-Index data structure
data FMIndex = FMIndex
  { bwt  :: [Char]             -- ^ Burrows-Wheeler Transform of the text
  , ctab :: [(Char, Int)]    -- ^ C table: cumulative character counts
  , occ  :: [(Char, [Int])]  -- ^ Occurrence table: counts of characters up to each position
  }