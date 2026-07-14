{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module BiFMIndex.BiBackwardSearch where

import FMIndex.Search (backwardSearch)
import FMIndex.Types (bwt, ctab)
import BiFMIndex.Types (BiFMIndex(..), BiRange(..), BiState(..))
import Data.ProofCombinators ((?))

{-@ offsetBackward :: st:BiState -> symbol:Char -> Nat @-}
offsetBackward :: BiState -> Char -> Int
offsetBackward st symbol = go (ctab (orig (index st)))
  where
    rng = origRange (range st)
    fi = orig (index st)

    {-@ go :: table:[(Char, Nat)] -> Nat @-}
    go :: [(Char, Int)] -> Int
    go [] = 0
    go ((c, _):cs)
      | c < symbol = let (s, e) = backwardSearch [c] fi rng
                     in (e - s) + go cs
      | otherwise  = go cs

-- | Teorema de partición del BWT bidireccional (Lam et al. 2009):
-- rLo + offset + (noHi - noLo) <= rHi, es decir, el nuevo extremo
-- superior del rango reverso queda dentro del rango reverso actual.
{-@ assume countBound
      :: off:Nat
      -> noLo:Nat
      -> noHi:{Nat | noLo <= noHi}
      -> rLo:Nat
      -> rHi:{Nat | rLo <= rHi}
      -> {v:() | rLo + off + noHi - noLo <= rHi} @-}
countBound :: Int -> Int -> Int -> Int -> Int -> ()
countBound _ _ _ _ _ = ()

-- | Extend the current pattern with one symbol.
{-@ biBackwardSearch :: BiState -> Char -> BiState @-}
biBackwardSearch :: BiState -> Char -> BiState
biBackwardSearch st symbol =
  BiState
    { index = bi
    , range = BiRange
        { pattern   = nextPattern
        , origRange = nextOrigRange
        , revRange  = nextRevRange
        }
    }
  where
    bi            = index st
    r             = range st
    nextPattern   = [symbol] ++ pattern r
    nextOrigRange = backwardSearch [symbol] (orig bi) (origRange r)

    rLo    = fst (revRange r)
    rHi    = snd (revRange r)
    offset = offsetBackward st symbol
    noLo   = fst nextOrigRange
    noHi   = snd nextOrigRange
    nrLo          = rLo + offset
    nrHi          = nrLo + (noHi - noLo) ? countBound offset noLo noHi rLo rHi
    nextRevRange  = (nrLo, nrHi)

{-@ biBackwardExtendExact :: BiState -> String -> BiState @-}
biBackwardExtendExact :: BiState -> String -> BiState
biBackwardExtendExact st s = go st (reverse s)
  where
    {-@ go :: BiState -> String -> BiState @-}
    go acc []     = acc
    go acc (c:cs) = go (biBackwardSearch acc c) cs
