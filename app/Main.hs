{-@ LIQUID "--reflection"     @-}

module Main where

import FMIndex.BWT ( buildBWT, buildSA )
import FMIndex.Types ( FMIndex(..) )
import FMIndex.Tables ( cTable, occTable )      
import FMIndex.Search ( backwardSearch, locate)
import BiFMIndex.BiFMIndex ( buildBiFMIndex, initializeBiState )
-- import BiFMIndex.BiForwardSearch ( biForwardSearch )
import BiFMIndex.BiBackwardSearch ( biBackwardSearch )
import BiFMIndex.Types ( BiState(..) )
-- import Alignment.BidirectionalSearch
--   ( biBackwardSearchSegment
--   , prefixExtension
--   , tryMismatch
--   )

-- {-@ ignore runCaseAStepByStep @-}
-- runCaseAStepByStep :: BiFMIndex -> IO ()
-- runCaseAStepByStep bi = do
--   let p = "enamoramiento"
--   let s1 = length p `div` 3
--   let s2 = 2 * length p `div` 3
--   let m = length p - 1
--   let initial = initializeBiState bi
--
--   putStrLn "\n=== Case A: flujo paso a paso ==="
--   putStrLn $ "Patron: " ++ show p
--   putStrLn $ "Split points: s1=" ++ show s1 ++ ", s2=" ++ show s2 ++ ", m=" ++ show m
--
--   let rangeP3 = biBackwardSearchSegment bi p s2 m initial
--   putStrLn $ "Paso 1 - Buscar P3 = P[s2-1..m] (0-index): " ++ show rangeP3
--
--   let prefixes_1 = prefixExtension bi p 1 s2 rangeP3
--   putStrLn "\nPaso 2 - Rangos exactos para prefijos (i, rangeI):"
--   print prefixes_1
--
--   let stepE2 = tryMismatch bi p prefixes_1
--   putStrLn "\nPaso 3 - Probar segunda discrepancia e2 en cada j:"
--   print stepE2
--
--   let prefixes_2 = concatMap (\(j, _, r) -> prefixExtension bi p 1 j r) stepE2
--   putStrLn "\nPaso 4 - Rangos exactos para prefijos (i, rangeI):"
--   print prefixes_2
--
--   let stepE1 = tryMismatch bi p prefixes_2
--   putStrLn "\nPaso 5 - Probar primera discrepancia e1 en cada i:"
--   print stepE1
--
--   let prefixes_3 = concatMap (\(j, _, r) -> prefixExtension bi p 0 j r) stepE1
--   putStrLn "\nPaso 6 - Rangos exactos para prefijos (i, rangeI):"
--   print prefixes_3


main :: IO ()
main = do
  let txt = "el xnxmoramiento es una locura"
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
                then "Original positions of pattern occurrences: " ++ show (locate fidx lo hi)
                else ("The index range is invalid: lo = " ++ show lo ++ ", hi = " ++ show hi ++ ", sa length = " ++ show (length (sa fidx)))

  let bi = buildBiFMIndex txt
  putStrLn $ "BiFMIndex: " ++ show bi
  let state_0 = initializeBiState bi
  putStrLn $ "Initial BiRange: " ++ show (range state_0)

  let state_1 = biBackwardSearch state_0 'n'
  putStrLn $ "Bidirectional backward search: " ++ show (range state_1)
  -- let state_2 = biForwardSearch state_1 'a'
  -- putStrLn $ "Bidirectional forward search: " ++ show (range state_2)
  -- let state_3 = biBackwardSearch state_2 'a'
  -- putStrLn $ "Bidirectional backward search: " ++ show (range state_3)
  -- let state_4 = biForwardSearch state_3 'n'
  -- putStrLn $ "Bidirectional forward search: " ++ show (range state_4)

  -- runCaseAStepByStep bi