{-@ LIQUID "--reflection"     @-}

module Main where

import FMIndex.BWT ( buildBWT )
import FMIndex.Types ( FMIndex(FMIndex) )
import FMIndex.Tables ( cTable, occTable )      
import FMIndex.Search ( backwardSearch )

main :: IO ()
main = do
  let txt = "banana"
  let bwt = buildBWT txt
  let cTab = cTable txt
  let occTab = occTable txt
  let fidx = FMIndex bwt cTab occTab (\c i -> ())

  putStrLn $ "Text: " ++ show txt
  putStrLn $ "BWT: " ++ show bwt
  putStrLn $ "C Table: " ++ show cTab
  putStrLn $ "Occ Table: " ++ show occTab
  let pattern = "ana"
  let (lo, hi) = backwardSearch pattern fidx
  putStrLn $ "Pattern: " ++ show pattern
  putStrLn $ "Occurrences in BWT range: [" ++ show lo ++ ", " ++ show hi ++ "]"

  
{-
main = do
  text <- loadGenome
  let biFM = buildBiFM text
  let graph = buildGraph biFM 25
  let scheme = generateScheme 2
  let matches = approxMatch biFM scheme 2 pattern
  print matches

-}