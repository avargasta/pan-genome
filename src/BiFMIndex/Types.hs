{-@ LIQUID "--reflection" @-}

module BiFMIndex.Types where

import FMIndex.Types ( FMIndex, bwt, Range(..) )

data BiRange = BiRange
  { origRange :: Range
  , revRange :: Range
  , pattern  :: String
  }

{-@ data BiRange = BiRange
  { origRange :: Range
  , revRange :: Range
  , pattern  :: [Char]
  } @-}

data BiFMIndex = BiFMIndex
  { orig :: FMIndex
  , rev :: FMIndex
  }

{-@ data BiFMIndex = BiFMIndex
  { orig :: FMIndex
  , rev  :: {r:FMIndex | len (bwt r) == len (bwt orig)}
  } @-}

data BiState = BiState
  { index :: BiFMIndex
  , range :: BiRange
  }

-- "lo <= hi" for each range is already guaranteed by the Range type itself;
-- only the BWT bound and the size-coupling invariant need to be stated here.
{-@ data BiState = BiState
  { index :: BiFMIndex
  , range :: {r:BiRange | hi (origRange r) <= len (bwt (orig index))
                        && hi (revRange r)  <= len (bwt (rev index))
                        && hi (origRange r) - lo (origRange r) == hi (revRange r) - lo (revRange r) }
  } @-}

--------------------------------------------------------------------------

instance Show BiFMIndex where
  show bi = "BiFMIndex { orig = " ++ show (orig bi)
           ++ ", rev = " ++ show (rev bi)
           ++ " }"

instance Show BiRange where
  show r = "BiRange { origRange = " ++ show (origRange r)
           ++ ", revRange = " ++ show (revRange r)
           ++ ", pattern = " ++ show (pattern r)
           ++ " }"

instance Show BiState where
  show st = "BiState { index = " ++ show (index st)
           ++ ", range = " ++ show (range st)
           ++ " }"