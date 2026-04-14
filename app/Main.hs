{-@ LIQUID "--reflection"     @-}

module Main where

import FMIndex.BWT ( buildBWT, buildSA )
import FMIndex.Types ( FMIndex(..) )
import FMIndex.Tables ( cTable, occTable )      
import FMIndex.Search ( backwardSearch, bwtRangeToOriginal )

main :: IO ()
main = do
  let txt = "banana"
  let bwt = buildBWT txt
  let cTab = cTable bwt
  let occTab = occTable bwt
  let suffix_array = buildSA txt
  putStrLn $ "Suffix Array: " ++ show suffix_array
  let fidx = FMIndex bwt cTab occTab suffix_array undefined
  let n = length bwt

  putStrLn $ "Text: " ++ show txt
  putStrLn $ "BWT: " ++ show bwt
  putStrLn $ "C Table: " ++ show cTab
  putStrLn $ "Occ Table: " ++ show occTab
  putStrLn $ "FM-Index built with BWT length: " ++ show n
  let pattern = "a"
  let (lo, hi) = backwardSearch pattern fidx
  putStrLn $ "Pattern: " ++ show pattern
  putStrLn $ "Occurrences in BWT range: [" ++ show lo ++ ", " ++ show hi ++ "]"
  putStrLn $ if lo < hi && hi <= length (sa fidx)
                then "Original positions of pattern occurrences: " ++ show (bwtRangeToOriginal fidx lo hi)
                else ("The index range is invalid: lo = " ++ show lo ++ ", hi = " ++ show hi ++ ", sa length = " ++ show (length (sa fidx)))
