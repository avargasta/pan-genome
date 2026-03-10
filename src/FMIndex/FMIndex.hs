module FMIndex.FMIndex where

import qualified Data.Vector.Unboxed as U
import Data.List --sortBy
import Data.Ord --comparing

-- type Interval = (Int, Int)

type SA = U.Vector Int
type BWT = U.Vector Char
-- type CTable = M.Map Char Int
-- type RankIndex = U.Vector Int

-- data FMIndex = FMIndex
--   { text     :: U.Vector Char
--   , sa       :: SA
--   , bwt      :: BWT
  -- , cTable   :: CTable
  -- , occTable :: M.Map Char RankIndex
  -- }

buildSA :: U.Vector Char -> SA
buildSA text = U.fromList sortedIndices -- buildSA text = ... → "the function takes text and returns …"
-- U.fromList sortedIndices → "what is returned is an efficient vector built from the list sortedIndices"
-- sortedIndices is computed in the where block using slices, sort, and map.
  where
    n = U.length text
    text' = text U.++ U.singleton '$'
    indices = [0..n]
    sortedIndices = map snd $ sortBy (comparing fst) [(U.slice i (n-i+1) text', i) | i <- indices]
    -- The list comprehension [(U.slice i (n-i+1) text', i) | i <- indices] generates tuples pairing each
    -- suffix (obtained by slicing from position i to the end) with its starting index. These tuples are sorted
    -- lexicographically using sortBy (comparing fst), which compares the first element of each tuple, i.e., the suffix.
    -- Finally, map snd extracts the original indices from the sorted tuples, producing sortedIndices, which is the suffix array.
    -- The U.fromList sortedIndices then converts this list into a U.Vector Int for efficient indexed access.


buildBWT :: U.Vector Char -> SA -> BWT
buildBWT text sa = U.map getPrevChar sa
  where
    n = U.length text
    getPrevChar i
      | i == 0  = '$'
      | otherwise = text U.! (i-1)

-- buildFM :: U.Vector Char -> FMIndex
-- buildFM = undefined

-- backwardExtend :: FMIndex -> Interval -> Char -> Interval
-- backwardExtend = undefined

-- lf :: FMIndex -> Int -> Int
-- lf = undefined

-- Programa principal de prueba
main :: IO ()
main = do
  let txt = U.fromList "banana"
  let sa = buildSA txt
  let bwt = buildBWT txt sa

  putStrLn $ "Text: " ++ show (U.toList txt)
  putStrLn $ "Suffix Array: " ++ show (U.toList sa)
  putStrLn $ "BWT: " ++ show (U.toList bwt)