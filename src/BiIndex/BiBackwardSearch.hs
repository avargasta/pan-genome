{-@ LIQUID "--reflection" @-}

module BiIndex.BiBackwardSearch where

import FMIndex.Search (backwardSearch)
import FMIndex.Types (bwt, ctab)
import BiIndex.Types (BiIndex(..), BiRange(..))

{-@ offsetBackward :: bi:BiIndex -> symbol:Char -> {v:(Nat, Nat) | fst v <= snd v && snd v <= len (bwt (fwd bi)) } -> Nat @-}
offsetBackward :: BiIndex -> Char -> (Int, Int) -> Int
offsetBackward bi symbol range = go (ctab (fwd bi))
  where
    {-@ go :: [(Char, _)] -> Nat @-}
    go [] = 0
    go ((c, _):cs)
      | c < symbol = let (s, e) = backwardSearch [c] (fwd bi) range
                     in (e - s) + go cs
      | otherwise  = go cs

-- | Extend the current pattern with one symbol.
{-@ biBackwardSearch :: bi:BiIndex -> range:{r:BiRange | fst (fwdRange r) <= snd (fwdRange r) && snd (fwdRange r) <= len (bwt (fwd bi)) && fst (bwdRange r) <= snd (bwdRange r) } -> symbol:Char -> {v:BiRange | fst (fwdRange v) <= snd (fwdRange v) && snd (fwdRange v) <= len (bwt (fwd bi)) && fst (bwdRange v) <= snd (bwdRange v) } @-}
biBackwardSearch :: BiIndex -> BiRange -> Char -> BiRange
biBackwardSearch bi range symbol =
  range
    { pattern = nextPattern
    , bwdRange = nextBwdRange
    , fwdRange = nextFwdRange
    }
  where
    nextPattern = [symbol] ++ pattern range
    lo' = fst (fwdRange range)
    hi' = snd (fwdRange range)
    nextFwdRange = backwardSearch [symbol] (fwd bi) (lo', hi')

    (flo, _) = bwdRange range
    offset    = offsetBackward bi symbol (lo', hi')
    (nbLo, nbHi) = nextFwdRange
    nextBwdLo     = flo + offset
    nextBwdHi     = flo + offset + (nbHi - nbLo)
    nextBwdRange  = (nextBwdLo, nextBwdHi)

-- | Extend the current pattern with an exact string (right to left).
{-@ biBackwardExtendExact :: bi:BiIndex
      -> range:{r:BiRange | fst (fwdRange r) <= snd (fwdRange r) && snd (fwdRange r) <= len (bwt (fwd bi)) && fst (bwdRange r) <= snd (bwdRange r) }
      -> s:String
      -> {v:BiRange | fst (fwdRange v) <= snd (fwdRange v) && snd (fwdRange v) <= len (bwt (fwd bi)) && fst (bwdRange v) <= snd (bwdRange v) } @-}
biBackwardExtendExact :: BiIndex -> BiRange -> String -> BiRange
biBackwardExtendExact bi range s = go range (reverse s)
  where
    {-@ go :: acc:{r:BiRange | fst (fwdRange r) <= snd (fwdRange r) && snd (fwdRange r) <= len (bwt (fwd bi)) && fst (bwdRange r) <= snd (bwdRange r) }
           -> t:String
           -> {v:BiRange | fst (fwdRange v) <= snd (fwdRange v) && snd (fwdRange v) <= len (bwt (fwd bi)) && fst (bwdRange v) <= snd (bwdRange v) } @-}
    go acc [] = acc
    go acc (c:cs) = go (biBackwardSearch bi acc c) cs
