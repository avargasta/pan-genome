{-@ LIQUID "--reflection"     @-}

module Main where

import FMIndex.BWT ( buildBWT, buildSA )
import FMIndex.Types ( FMIndex(..) )
import FMIndex.Tables ( cTable, occTable )      
import FMIndex.Search ( backwardSearch, bwtRangeToOriginal )
import BiIndex.BiIndex ( buildBiIndex, initializeBiRange )
import BiIndex.BiForwardSearch ( biForwardSearch )
import BiIndex.BiBackwardSearch ( biBackwardSearch )
import BiIndex.Types ( BiIndex(..), BiRange(..) )
import Data.ProofCombinators ( assume )

main :: IO ()
main = do
  let txt = "banana"
  let bwt_txt = buildBWT txt
  let cTab = cTable bwt_txt
  let occTab = occTable bwt_txt
  let suffix_array = buildSA txt
  putStrLn $ "Suffix Array: " ++ show suffix_array
  let fidx = FMIndex bwt_txt cTab occTab suffix_array undefined
  let n = length bwt_txt

  putStrLn $ "Text: " ++ show txt
  putStrLn $ "BWT: " ++ show bwt_txt
  putStrLn $ "C Table: " ++ show cTab
  putStrLn $ "Occ Table: " ++ show occTab
  putStrLn $ "FM-Index built with BWT length: " ++ show n
  let patt = "a"
  let (lo, hi) = backwardSearch patt fidx (0, n)
  putStrLn $ "Pattern: " ++ show patt
  putStrLn $ "Occurrences in BWT range: [" ++ show lo ++ ", " ++ show hi ++ "]"
  putStrLn $ if lo < hi && hi <= length (sa fidx)
                then "Original positions of pattern occurrences: " ++ show (bwtRangeToOriginal fidx lo hi)
                else ("The index range is invalid: lo = " ++ show lo ++ ", hi = " ++ show hi ++ ", sa length = " ++ show (length (sa fidx)))

  let bi = buildBiIndex txt
  putStrLn $ "BiIndex: " ++ show bi
  let biRange_0 = initializeBiRange bi
  putStrLn $ "Initial BiRange: " ++ show biRange_0

  let biRange_0' = assume (fst (fwdRange biRange_0) <= snd (fwdRange biRange_0) && snd (fwdRange biRange_0) <= length (bwt (fwd bi)) && fst (bwdRange biRange_0) <= snd (bwdRange biRange_0) && snd (bwdRange biRange_0) <= length (bwt (bwd bi))) biRange_0
  let biRange_1 = biBackwardSearch bi biRange_0' 'n'
  putStrLn $ "Bidirectional backward search: " ++ show biRange_1
  let biRange_1' = assume (fst (fwdRange biRange_1) <= snd (fwdRange biRange_1) && snd (fwdRange biRange_1) <= length (bwt (fwd bi)) && fst (bwdRange biRange_1) <= snd (bwdRange biRange_1) && snd (bwdRange biRange_1) <= length (bwt (bwd bi))) biRange_1
  let biRange_2 = biForwardSearch bi biRange_1' 'a'
  putStrLn $ "Bidirectional forward search: " ++ show biRange_2
  let biRange_2' = assume (fst (fwdRange biRange_2) <= snd (fwdRange biRange_2) && snd (fwdRange biRange_2) <= length (bwt (fwd bi)) && fst (bwdRange biRange_2) <= snd (bwdRange biRange_2) && snd (bwdRange biRange_2) <= length (bwt (bwd bi))) biRange_2
  let biRange_3 = biBackwardSearch bi biRange_2' 'a'
  putStrLn $ "Bidirectional backward search: " ++ show biRange_3
  let biRange_3' = assume (fst (fwdRange biRange_3) <= snd (fwdRange biRange_3) && snd (fwdRange biRange_3) <= length (bwt (fwd bi)) && fst (bwdRange biRange_3) <= snd (bwdRange biRange_3) && snd (bwdRange biRange_3) <= length (bwt (bwd bi))) biRange_3
  let biRange_4 = biForwardSearch bi biRange_3' 'n'
  putStrLn $ "Bidirectional forward search: " ++ show biRange_4