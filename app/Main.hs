module Main where

main :: IO ()
main = putStrLn "Hello, world!"


{-
main = do
  text <- loadGenome
  let biFM = buildBiFM text
  let graph = buildGraph biFM 25
  let scheme = generateScheme 2
  let matches = approxMatch biFM scheme 2 pattern
  print matches

-}