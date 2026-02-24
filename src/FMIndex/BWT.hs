module FMIndex.BWT
  ( BWT
  , CTable
  , buildBWT
  , buildCTable
  ) where


type BWT = U.Vector Char
type CTable = Map Char Int


buildBWT :: U.Vector Char -> SA -> BWT
buildCTable :: BWT -> CTable
buildBWT = undefined
buildCTable = undefined