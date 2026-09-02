{-@ LIQUID "--reflection" @-}

module ApproximateSearch.SeedPieces where

import ApproximateSearch.Types (Coverage)

-- | Split a pattern into `n` contiguous pieces covering it fully, as equal
--   in length as possible (the first `length p `mod` n` pieces get one
--   extra character). By the pigeonhole principle, an occurrence with at
--   most `n - 1` mismatches must match at least one piece exactly.
{-@ seedPieces :: p:String -> n:{Nat | 0 < n} -> [(String, Coverage)] @-}
seedPieces :: String -> Int -> [(String, Coverage)]
seedPieces p n = go 0 0
  where
    len   = length p
    base  = len `div` n
    extra = len `mod` n

    {-@ go :: i:{Nat | i <= n} -> Nat -> [(String, Coverage)] / [n - i] @-}
    go :: Int -> Int -> [(String, Coverage)]
    go i start
      | i >= n    = []
      | otherwise = (piece, (start, end)) : go (i + 1) end
      where
        pieceLen = base + (if i < extra then 1 else 0)
        end      = start + pieceLen
        piece    = take pieceLen (drop start p)
