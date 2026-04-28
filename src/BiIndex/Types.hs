{-@ LIQUID "--reflection" @-}

module BiIndex.Types where

import FMIndex.Types ( FMIndex, bwt )

data BiIndex = BiIndex
  { fwd :: FMIndex
  , bwd :: FMIndex
  }

{-@ data BiIndex = BiIndex
      { fwd :: FMIndex
      , bwd :: FMIndex
      } @-}

data BiRange = BiRange
  { fwdRange :: (Int, Int)
  , bwdRange :: (Int, Int)
  , pattern  :: String
  }

{-@ data BiRange = BiRange
  { fwdRange :: (Nat, Nat)
  , bwdRange :: (Nat, Nat)
  , pattern  :: [Char]
  } @-}

instance Show BiIndex where
  show bi = "BiIndex { fwd = " ++ show (fwd bi)
           ++ ", bwd = " ++ show (bwd bi)
           ++ " }"

instance Show BiRange where
  show r = "BiRange { fwdRange = " ++ show (fwdRange r)
           ++ ", bwdRange = " ++ show (bwdRange r)
           ++ ", pattern = " ++ show (pattern r)
           ++ " }" 