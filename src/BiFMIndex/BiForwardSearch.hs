{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module BiFMIndex.BiForwardSearch where

import FMIndex.Search (backwardSearch)
import FMIndex.Types (bwt, ctab)
import BiFMIndex.Types (BiFMIndex(..), BiRange(..), BiState(..))
import Data.ProofCombinators ((?))

{-@ offsetForward :: st:BiState -> symbol:Char -> Nat @-}
offsetForward :: BiState -> Char -> Int
offsetForward st symbol = go (ctab (rev (index st)))
  where
    rng = revRange (range st)
    fi  = rev (index st)

    {-@ go :: table:[(Char, Nat)] -> Nat @-}
    go :: [(Char, Int)] -> Int
    go [] = 0
    go ((c, _):cs)
      | c < symbol = let (s, e) = backwardSearch [c] fi rng
                     in (e - s) + go cs
      | otherwise  = go cs

-- | Bidirectional BWT partition theorem (Lam et al. 2009):
-- oLo + offset + (nrHi - nrLo) <= oHi, i.e., the new upper
-- bound of the original range lies within the current original range.
{-@ assume countBoundFwd
      :: off:Nat
      -> nrLo:Nat
      -> nrHi:{Nat | nrLo <= nrHi}
      -> oLo:Nat
      -> oHi:{Nat | oLo <= oHi}
      -> {v:() | oLo + off + nrHi - nrLo <= oHi} @-}
countBoundFwd :: Int -> Int -> Int -> Int -> Int -> ()
countBoundFwd _ _ _ _ _ = ()

-- | Extend the current pattern with one symbol.
{-@ biForwardSearch :: BiState -> Char -> BiState @-}
biForwardSearch :: BiState -> Char -> BiState
biForwardSearch st symbol =
  BiState
    { index = bi
    , range = BiRange
        { pattern   = nextPattern
        , origRange = nextOrigRange
        , revRange  = nextRevRange
        }
    }
  where
    bi           = index st
    r            = range st
    nextPattern  = pattern r ++ [symbol]
    nextRevRange = backwardSearch [symbol] (rev bi) (revRange r)

    oLo    = fst (origRange r)
    oHi    = snd (origRange r)
    offset = offsetForward st symbol
    nrLo   = fst nextRevRange
    nrHi   = snd nextRevRange
    noLo          = oLo + offset
    noHi          = noLo + (nrHi - nrLo) ? countBoundFwd offset nrLo nrHi oLo oHi
    nextOrigRange = (noLo, noHi)

{-@ biForwardExtendExact :: BiState -> String -> BiState @-}
biForwardExtendExact :: BiState -> String -> BiState
biForwardExtendExact st s = go st s
  where
    {-@ go :: BiState -> String -> BiState @-}
    go acc []     = acc
    go acc (c:cs) = go (biForwardSearch acc c) cs
