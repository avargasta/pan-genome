module FMIndex where

import qualified Data.Vector.Unboxed as U

type Interval = (Int, Int)

data FMIndex = FMIndex
  { text     :: U.Vector Char
  , sa       :: SA
  , bwt      :: BWT
  , cTable   :: CTable
  , occTable :: Map Char RankIndex
  }


buildFM :: U.Vector Char -> FMIndex
buildFM = undefined

backwardExtend :: FMIndex -> Interval -> Char -> Interval
backwardExtend = undefined

lf :: FMIndex -> Int -> Int
lf = undefined 