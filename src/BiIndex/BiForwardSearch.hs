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
--   Updates bwdRange by running backward search on reverse pattern over bwd index.
{-@ biForwardSearch
      :: bi:BiIndex
      -> range:{r:BiRange
      | fst (fwdRange r) <= snd (fwdRange r)
      && snd (fwdRange r) <= len (bwt (fwd bi))
      && fst (bwdRange r) <= snd (bwdRange r)
      && snd (bwdRange r) <= len (bwt (bwd bi)) }
      -> symbol:Char
      -> BiRange
  @-}
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
