{-@ LIQUID "--reflection"     @-}

module Main where

import FMIndex.BWT ( buildBWT, buildSA )
import FMIndex.Types ( FMIndex(..) )
import FMIndex.Tables ( cTable, occTable )      
import FMIndex.Search ( backwardSearch, locate)
import BiFMIndex.BiFMIndex ( buildBiFMIndex, initializeBiState )
-- import BiFMIndex.BiForwardSearch ( biForwardSearch )
import BiFMIndex.BiBackwardSearch ( biBackwardSearch, biBackwardExtendExact )
import BiFMIndex.Types ( BiFMIndex, BiState(..) )
import Alignment.BidirectionalSearch ( prefixExtension, prefixMismatch )

-- | Step-by-step walkthrough of the 2-mismatch search for pattern
--   "dignifica" against a text that contains two occurrences of it: one with
--   mismatches at pattern positions 0 and 1 ("xxgnifica"), one with
--   mismatches at positions 1 and 4 ("dxgnxfica").
--
--   At every step we pass the whole pattern @p@, even though the entries in
--   a list can sit at different positions: both 'prefixExtension' and
--   'prefixMismatch' index into it absolutely from each entry's own @pos@,
--   so a single shared call handles the whole (possibly mixed-position)
--   branch list at once.
{-@ ignore runDignificaWalkthrough @-}
runDignificaWalkthrough :: BiFMIndex -> IO ()
runDignificaWalkthrough bi = do
  let p       = "dignifica"
  let initial = initializeBiState bi

  putStrLn "\n=== Walkthrough: pattern \"dignifica\", 2 allowed mismatches ==="
  putStrLn $ "Patron: " ++ show p

  -- 1. biBackwardExtendExact: exact match of the error-free suffix "ica".
  let suffix = "ica"
  let pos1   = length p - length suffix
  let st1    = biBackwardExtendExact initial suffix
  putStrLn $ "\n1. biBackwardExtendExact " ++ show suffix ++ " (pos=" ++ show pos1 ++ "):"
  print (range st1)

  -- 2. prefixExtension: extend left, checkpointing at every narrowing/wall.
  let e2 = prefixExtension [(st1, pos1)] p
  putStrLn "\n2. prefixExtension:"
  mapM_ (\(st, pos) -> putStrLn $ show pos ++ " -> " ++ show (range st)) e2

  -- 3. prefixMismatch: try a mismatch right before each checkpoint. e2 has
  --    entries at different positions, but prefixMismatch now looks up each
  --    one's own correct character via `p !! (pos - 1)`, so one shared call
  --    over the whole list (no concatMap needed) is enough.
  let e3 = prefixMismatch e2 p
  putStrLn "\n3. prefixMismatch:"
  mapM_ (\(st, pos) -> putStrLn $ show pos ++ " -> " ++ show (range st)) e3

  -- 4. prefixExtension: extend each mismatch branch to its next wall. e3 has
  --    entries at different positions, but prefixExtension now walks each
  --    one from its own `pos - 1` down to 0 within the shared p, so one call
  --    over the whole list is enough.
  let e4 = prefixExtension e3 p
  putStrLn "\n4. prefixExtension:"
  mapM_ (\(st, pos) -> putStrLn $ show pos ++ " -> " ++ show (range st)) e4

  -- 5. prefixMismatch: the second mismatch per branch, same reasoning as (3).
  let e5 = prefixMismatch e4 p
  putStrLn "\n5. prefixMismatch:"
  mapM_ (\(st, pos) -> putStrLn $ show pos ++ " -> " ++ show (range st)) e5

  -- 6. prefixExtension: final exact extension down to the start of p.
  let e6 = prefixExtension e5 p
  putStrLn "\n6. prefixExtension (final):"
  mapM_ (\(st, pos) -> putStrLn $ show pos ++ " -> " ++ show (range st)) e6


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

  let txt2 = "el trabajo no xxgnifica, lo que dxgnxfica es el tiempo libre"
  let bi2  = buildBiFMIndex txt2
  runDignificaWalkthrough bi2