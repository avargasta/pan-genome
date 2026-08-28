{-@ LIQUID "--reflection"     @-}

module Main where

import FMIndex.Search ( locate )
import BiFMIndex.BiFMIndex ( buildBiFMIndex, initializeBiState )
import BiFMIndex.BiBackwardSearch ( biBackwardExtendExact )
import BiFMIndex.BiForwardSearch ( biForwardExtendExact )
import BiFMIndex.Types ( BiFMIndex(..), BiState(..), BiRange(..) )
import Alignment.BidirectionalSearch ( prefixExtension, prefixMismatch, suffixExtension )

-- | Print one (state, (start, end)) branch of the search: the slice
--   P[start..end) of the read that this branch currently represents, the
--   FM-index range it corresponds to, and the positions in T where it
--   actually occurs (obtained via 'locate').
{-@ ignore showBranch @-}
showBranch :: (BiState, (Int, Int)) -> IO ()
showBranch (st, (start, end)) = do
  let br       = biRange st
  let (lo, hi) = range br
  let occs
        | lo < hi   = show (locate (fmidx (biIndex st)) lo hi)
        | otherwise = "[]  (no occurrences left)"
  putStrLn $ "    P[" ++ show start ++ ".." ++ show end ++ ") = " ++ show (pattern br)
           ++ "   range=" ++ show (lo, hi) ++ "   positions in T=" ++ occs

-- | Walkthrough of approximate matching for the read P = "banana" against
--   the text T = "bananacanana", with one allowed substitution (k = 1).
--
--   By the pigeonhole argument, splitting P into k+1 = 2 pieces guarantees
--   that at least one of them occurs exactly. Here we search both pieces
--   as seeds and extend each of them over the rest of P:
--     * P1 = "ban" = P[0..3), extended to the right with 'suffixExtension'.
--     * P2 = "ana" = P[3..6), extended to the left with 'prefixExtension'
--       and 'prefixMismatch'.
--
--   T contains two occurrences of interest: "banana" itself at position 0
--   (an exact match), and "canana" at position 6, which differs from P
--   only in its first character (a match at Hamming distance 1).
{-@ ignore runBananaWalkthrough @-}
runBananaWalkthrough :: BiFMIndex -> IO ()
runBananaWalkthrough bi = do
  let t       = "bananacanana"
  let p       = "banana"
  let initial = initializeBiState bi

  putStrLn "\n=== Walkthrough: read P = \"banana\" against T = \"bananacanana\", k = 1 ==="
  putStrLn $ "Text T: " ++ show t
  putStrLn $ "Read P: " ++ show p
  putStrLn "Partition into k+1 = 2 pieces: P1 = \"ban\" = P[0..3), P2 = \"ana\" = P[3..6)."

  -- Seed 1: P1 = "ban" -------------------------------------------------
  putStrLn "\n--- Seed 1: P1 = \"ban\" ---"

  putStrLn "1. Exact search of P1 with biBackwardExtendExact:"
  let st1 = biBackwardExtendExact initial "ban"
  showBranch (st1, (0, 3))

  putStrLn "\n2. suffixExtension: grow the seed to the right, one character of P"
  putStrLn "   at a time. \"ban\" occurs only once in T, so every step below stays"
  putStrLn "   exact (the range never narrows): the seed extends all the way to a"
  putStrLn "   full, exact occurrence of P without ever needing a mismatch."
  let e2 = suffixExtension [(st1, (0, 3))] p
  mapM_ showBranch e2

  -- Seed 2: P2 = "ana" -------------------------------------------------
  putStrLn "\n--- Seed 2: P2 = \"ana\" ---"

  putStrLn "3. Exact search of P2 with biForwardExtendExact:"
  let st2 = biForwardExtendExact initial "ana"
  showBranch (st2, (3, 6))

  putStrLn "\n4. prefixExtension: grow the seed to the left, one character of P at"
  putStrLn "   a time. \"ana\" occurs four times in T, but not all four are preceded"
  putStrLn "   by the same characters of P, so the range narrows along the way."
  putStrLn "   Each narrowing step is recorded as a checkpoint -- the state just"
  putStrLn "   before the failed exact addition -- for a later mismatch to resume"
  putStrLn "   from; the walk itself keeps going with the smaller, still-exact range."
  let e4 = prefixExtension [(st2, (3, 6))] p
  mapM_ showBranch e4

  putStrLn "\n5. prefixMismatch: from each checkpoint recorded in step 4, try every"
  putStrLn "   other alphabet character at that position, spending the mismatch"
  putStrLn "   budget (k = 1). One of the resulting branches reaches P[0..6) with"
  putStrLn "   pattern \"canana\" at position 6: the approximate occurrence of P at"
  putStrLn "   Hamming distance 1 that this seed was looking for. The remaining"
  putStrLn "   branches are partial re-explorations of the exact occurrence already"
  putStrLn "   found in full via seed 1."
  let e5 = prefixMismatch e4 p
  mapM_ showBranch e5

  putStrLn "\n6. prefixExtension: keep growing the step-5 branches to the left, to"
  putStrLn "   check whether \"babana\" or \"bacana\" -- the two ways of completing"
  putStrLn "   \"bana\"/\"cana\" back to a full occurrence of P -- actually occur in T."
  putStrLn "   \"cana\" first extends exactly to \"acana\" (which does occur), then"
  putStrLn "   fails on the next character: \"bacana\" is not in T, so it stops one"
  putStrLn "   character short. \"bana\" fails immediately: it sits at the very start"
  putStrLn "   of T, so there is no character to its left at all, and \"babana\" is"
  putStrLn "   ruled out the same way. Only the branch already at P[0..6) -- the"
  putStrLn "   \"canana\" match found in step 5 -- survives untouched."
  let e6 = prefixExtension e5 p
  mapM_ showBranch e6

main :: IO ()
main = do
  let t  = "bananacanana"
  let bi = buildBiFMIndex t
  runBananaWalkthrough bi
