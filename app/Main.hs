module Main where

main :: IO ()
main = do
  let txt = "banana"
--   let sa = buildSA txt
--   let bwt = buildBWT txt sa

  putStrLn $ "Text: " ++ show txt
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