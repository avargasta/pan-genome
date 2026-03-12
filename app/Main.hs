module Main where

import qualified Data.Vector.Unboxed as U
-- import FMIndex.FMIndex

main :: IO ()
main = do
  let txt = U.fromList "banana"
--   let sa = buildSA txt
--   let bwt = buildBWT txt sa

  putStrLn $ "Text: " ++ show (U.toList txt)
--   putStrLn $ "Suffix Array: " ++ show (U.toList sa)
--   putStrLn $ "BWT: " ++ show (U.toList bwt)
  
{-
main = do
  text <- loadGenome
  let biFM = buildBiFM text
  let graph = buildGraph biFM 25
  let scheme = generateScheme 2
  let matches = approxMatch biFM scheme 2 pattern
  print matches

-}