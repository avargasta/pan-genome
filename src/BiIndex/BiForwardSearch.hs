
{-@ LIQUID "--reflection" @-}

module BiIndex.BiForwardSearch where

import FMIndex.Search (backwardSearch)
import FMIndex.Types (bwt, ctab)
import BiIndex.Types (BiIndex(..), BiRange(..))

{-@ offsetForward :: bi:BiIndex -> symbol:Char -> {v:(Nat, Nat) | fst v <= snd v && snd v <= len (bwt (bwd bi)) } -> Nat @-}
offsetForward :: BiIndex -> Char -> (Int, Int) -> Int
offsetForward bi symbol range = go (ctab (bwd bi))
  where
    {-@ go :: [(Char, _)] -> Nat @-}
    go [] = 0
    go ((c, _):cs)
      | c < symbol = let (s, e) = backwardSearch [c] (bwd bi) range
                     in (e - s) + go cs
      | otherwise  = go cs

-- | Extend the current pattern with one symbol.
{-@ biForwardSearch :: bi:BiIndex -> range:{r:BiRange | fst (fwdRange r) <= snd (fwdRange r) && fst (bwdRange r) <= snd (bwdRange r) && snd (bwdRange r) <= len (bwt (bwd bi)) } -> symbol:Char -> {v:BiRange | fst (fwdRange v) <= snd (fwdRange v) && fst (bwdRange v) <= snd (bwdRange v) && snd (bwdRange v) <= len (bwt (bwd bi)) } @-}
biForwardSearch :: BiIndex -> BiRange -> Char -> BiRange
biForwardSearch bi range symbol =
  range
    { pattern = nextPattern
    , bwdRange = nextBwdRange
    , fwdRange = nextFwdRange
    }
  where
    nextPattern = pattern range ++ [symbol]
    lo' = fst (bwdRange range)
    hi' = snd (bwdRange range)
    nextBwdRange = backwardSearch [symbol] (bwd bi) (lo', hi')

    (flo, _) = fwdRange range
    offset    = offsetForward bi symbol (lo', hi')
    (nbLo, nbHi) = nextBwdRange
    nextFwdLo     = flo + offset
    nextFwdHi     = flo + offset + (nbHi - nbLo)
    nextFwdRange  = (nextFwdLo, nextFwdHi)

-- | Extend the current pattern with an exact string (left to right).
{-@ biForwardExtendExact :: bi:BiIndex
      -> range:{r:BiRange | fst (fwdRange r) <= snd (fwdRange r) && fst (bwdRange r) <= snd (bwdRange r) && snd (bwdRange r) <= len (bwt (bwd bi)) }
      -> s:String
      -> {v:BiRange | fst (fwdRange v) <= snd (fwdRange v) && fst (bwdRange v) <= snd (bwdRange v) && snd (bwdRange v) <= len (bwt (bwd bi)) } @-}
biForwardExtendExact :: BiIndex -> BiRange -> String -> BiRange
biForwardExtendExact bi range s = go range s
  where
    {-@ go :: acc:{r:BiRange | fst (fwdRange r) <= snd (fwdRange r) && fst (bwdRange r) <= snd (bwdRange r) && snd (bwdRange r) <= len (bwt (bwd bi)) }
           -> t:String
           -> {v:BiRange | fst (fwdRange v) <= snd (fwdRange v) && fst (bwdRange v) <= snd (bwdRange v) && snd (bwdRange v) <= len (bwt (bwd bi)) } @-}
    go acc [] = acc
    go acc (c:cs) = go (biForwardSearch bi acc c) cs
