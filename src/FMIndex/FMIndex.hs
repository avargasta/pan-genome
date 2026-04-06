{-@ LIQUID "--reflection" @-}

module FMIndex.FMIndex
(FMIndex', mkFMIndex) where

import FMIndex.BWT    (buildBWT)
import FMIndex.Types  (FMIndex(..))
import FMIndex.Tables (cTable, occTable, cLookup, occLookup)


data FMIndex' = FMIndex'
  { bwt'    :: [Char]
  , ctab'   :: [(Char, Int)]
  , occtab' :: [(Char, [Int])]
  }

{-@ data FMIndex' = FMIndex'
   { bwt'    :: {v:[Char] | 1 <= len v}
   , ctab'   :: [(Char, {v:Nat | v <= len bwt'})]
   , occtab' :: [(Char, {xs:SortedList Nat | len bwt' + 1 == len xs})]
   } @-}

-- Constructor inteligente que carga el invariante
{-@ mkFMIndex :: bwt' : {v:[Char] | 1 <= len v} -> ctab' : [(Char, {v:Nat | v <= len bwt'})] -> occtab' : [(Char, {xs:SortedList Nat | len bwt' + 1 == len xs})] -> inv' : (c : Char -> i : {Nat | i <= len bwt'} -> {v:() | cLookup c ctab' + occLookup c i occtab' <= len bwt'}) -> FMIndex' @-}
mkFMIndex :: [Char] -> [(Char,Int)] -> [(Char,[Int])] -> (Char -> Int -> ()) -> FMIndex'
mkFMIndex b c o _ = FMIndex' b c o

-- {-@ buildFMIndex :: {v:[Char] | 1 <= len v} -> FMIndex' @-}
-- buildFMIndex' :: [Char] -> FMIndex'
-- buildFMIndex' t = mkFMIndex bwt' ctab' occtab' inv'
--   where
--     bwt'    = buildBWT t
--     ctab'   = cTable t
--     occtab' = occTable t

--     {-@ inv' :: c:Char 
--              -> i:{Nat | i <= len bwt'} 
--              -> {v:() | cLookup c ctab' + occLookup c i occtab' <= len bwt'} @-}
--     inv' :: Char -> Int -> ()
--     inv' _ _ = ()