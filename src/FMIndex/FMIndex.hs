module FMIndex.FMIndex where

import Data.List ( sort, nub )
-- import qualified Data.Vector.Unboxed as U
-- import Data.Ord --comparing
-- import Data.List (sort, elemIndex)
-- import Data.Maybe (fromJust)
-- import Data.Maybe (fromMaybe)
-- import qualified Data.Map as M


-- -- type Interval = (Int, Int)

-- type SA = U.Vector Int
-- type BWT = U.Vector Char
-- -- type CTable = M.Map Char Int
-- -- type RankIndex = U.Vector Int

-- -- data FMIndex = FMIndex
-- --   { text     :: U.Vector Char
-- --   , sa       :: SA
-- --   , bwt      :: BWT
--   -- , cTable   :: CTable
--   -- , occTable :: M.Map Char RankIndex
--   -- }

-- buildSA :: U.Vector Char -> SA
-- buildSA text = U.fromList sortedIndices -- buildSA text = ... → "the function takes text and returns …"
-- -- U.fromList sortedIndices → "what is returned is an efficient vector built from the list sortedIndices"
-- -- sortedIndices is computed in the where block using slices, sort, and map.
--   where
--     n = U.length text
--     text' = text U.++ U.singleton '$'
--     indices = [0..n]
--     sortedIndices = map snd $ sortBy (comparing fst) [(U.slice i (n-i+1) text', i) | i <- indices]
--     -- The list comprehension [(U.slice i (n-i+1) text', i) | i <- indices] generates tuples pairing each
--     -- suffix (obtained by slicing from position i to the end) with its starting index. These tuples are sorted
--     -- lexicographically using sortBy (comparing fst), which compares the first element of each tuple, i.e., the suffix.
--     -- Finally, map snd extracts the original indices from the sorted tuples, producing sortedIndices, which is the suffix array.
--     -- The U.fromList sortedIndices then converts this list into a U.Vector Int for efficient indexed access.


-- buildBWT :: U.Vector Char -> SA -> BWT
-- buildBWT text sa = U.map getPrevChar sa
--   where
--     n = U.length text
--     getPrevChar i
--       | i == 0  = '$'
--       | otherwise = text U.! (i-1)

-- -- buildFM :: U.Vector Char -> FMIndex
-- -- buildFM = undefined

-- -- backwardExtend :: FMIndex -> Interval -> Char -> Interval
-- -- backwardExtend = undefined

-- -- lf :: FMIndex -> Int -> Int
-- -- lf = undefined


{-@ rotate :: {v:[Char] | len v > 0} -> {v:[Char] | len v > 0} @-}
rotate :: [Char] -> [Char]
rotate (y:ys) = ys ++ [y]

{-@ rotations :: {xs:[Char] | len xs > 0} -> [{v:[Char] | len v > 0}] @-}
rotations :: [Char] -> [[Char]]
rotations xs = take (length xs) (iterate rotate xs)

{-@ bwt_f :: {s:[Char] | len s > 0} -> [Char] @-}
bwt_f :: [Char] -> [Char]
bwt_f s = l
  where
    rs = rotations s
    m  = sort rs
    l  = map last m

cTable :: [Char] -> [(Char, Int)]
cTable s = go (sort s) 0 []
  where
    go [] _ acc = acc
    go (x:xs) i acc
      | x `elem` map fst acc = go xs (i+1) acc
      | otherwise            = go xs (i+1) ((x,i):acc)

occ :: [Char] -> Char -> Int -> Int
occ l c i = length (filter (== c) (take (i+1) l))

{-@ occTable :: {s:[Char] | len s > 0} -> [(Char,[Int])] @-}
occTable :: [Char] -> [(Char,[Int])]
occTable s = [(c, occList c) | c <- alphabet]
  where
    l = bwt_f s
    alphabet = nub l
    n = length l

    occList c = [occ l c i | i <- [0..n-1]]