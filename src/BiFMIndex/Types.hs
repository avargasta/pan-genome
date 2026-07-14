{-@ LIQUID "--reflection" @-}

module BiFMIndex.Types where

import FMIndex.Types ( FMIndex, bwt )

data BiFMIndex = BiFMIndex
  { orig :: FMIndex
  , rev :: FMIndex
  }

{-@ data BiFMIndex = BiFMIndex
  { orig :: FMIndex
  , rev  :: {r:FMIndex | len (bwt r) == len (bwt orig)}
  } @-}

data BiRange = BiRange
  { origRange :: (Int, Int)
  , revRange :: (Int, Int)
  , pattern  :: String
  }

{-@ data BiRange = BiRange
  { origRange :: (Nat, Nat)
  , revRange :: (Nat, Nat)
  , pattern  :: [Char]
  } @-}

instance Show BiFMIndex where
  show bi = "BiFMIndex { orig = " ++ show (orig bi)
           ++ ", rev = " ++ show (rev bi)
           ++ " }"

instance Show BiRange where
  show r = "BiRange { origRange = " ++ show (origRange r)
           ++ ", revRange = " ++ show (revRange r)
           ++ ", pattern = " ++ show (pattern r)
           ++ " }"

data BiState = BiState
  { index :: BiFMIndex
  , range :: BiRange
  }
  

{-@ data BiState = BiState
  { index :: BiFMIndex
  , range :: {r:BiRange | fst (origRange r) <= snd (origRange r)
                        && snd (origRange r) <= len (bwt (orig index))
                        && fst (revRange r) <= snd (revRange r)
                        && snd (revRange r) <= len (bwt (rev index))
                        && snd (origRange r) - fst (origRange r) == snd (revRange r) - fst (revRange r) }
  } @-}

instance Show BiState where
  show st = "BiState { index = " ++ show (index st)
           ++ ", range = " ++ show (range st)
           ++ " }"