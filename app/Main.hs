{-@ LIQUID "--reflection"     @-}

module Main where

import BiFMIndex.BiFMIndex ( buildBiFMIndex )
import ApproximateSearch.ApproximateSearch ( approximateSearch )

-- | T is built from five variants of P = "abcdef" (separated by '0' so they
--   can't bleed into one another), each at a known Hamming distance from P:
--     seg1 = "abcdef"  distance 0 (exact)
--     seg2 = "abcdeg"  distance 1 (position 5: f -> g)
--     seg3 = "abpdef"  distance 1 (position 2: c -> p)
--     seg4 = "xbcdeg"  distance 2 (positions 0 and 5)
--     seg5 = "xbpdeg"  distance 3 (positions 0, 2 and 5)
--   Increasing k should pull seg2/seg3 in at k=1 and seg4 in at k=2, while
--   seg5 (distance 3) never qualifies for any k tried here.
main :: IO ()
main = do
  let seg1 = "abcdef"
      seg2 = "abcdeg"
      seg3 = "abpdef"
      seg4 = "xbcdeg"
      seg5 = "xbpdeg"
      t    = seg1 ++ "0" ++ seg2 ++ "0" ++ seg3 ++ "0" ++ seg4 ++ "0" ++ seg5
      p    = "abcdef"
      bi   = buildBiFMIndex t

  putStrLn $ "Text T: " ++ show t
  putStrLn $ "Read P: " ++ show p
  putStrLn ""
  mapM_
    (\k -> putStrLn $ "approximateSearch bi p " ++ show k ++ " = " ++ show (approximateSearch bi p k))
    [0, 1, 2 :: Int]
