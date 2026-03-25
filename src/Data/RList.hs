{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ infix :               @-}
module Data.RList where

import Language.Haskell.Liquid.ProofCombinators

{-@ type SortedList a = [a]<{\i j -> i <= j}>  @-} -- Expressing sortedness using abstract refinements  


{-@ reflect index @-}
{-@ index :: xs:[a] -> {v:Int | 0 <= v && v < len xs} -> a @-}
index :: [a] -> Int -> a
index (x:_) 0 = x
index (_:xs) n = index xs (n-1)

{-@ lookupSorted :: x:a -> xs:SortedList {y:a | x <= y} -> i:{Nat | i < len xs + 1} 
                 -> { x <= index (x:xs) i } @-}
lookupSorted :: Ord a => a -> [a] -> Int -> ()
lookupSorted x [] _ = ()
lookupSorted x (y:ys) i
    | i == 0    = ()
    | otherwise = lookupSorted y ys (i-1) 


{-@ incrLookUpSorted :: xs: SortedList a  
                     -> i:Nat
                     -> j:{Nat | i <= j && j < len xs}
                     -> { index xs i <= index xs j } @-}
incrLookUpSorted :: Ord a => [a] -> Int -> Int -> ()
incrLookUpSorted (x:xs) 0 j =
    if j == 0 then () else lookupSorted x xs j 
incrLookUpSorted (x:xs) i 0 = ()
incrLookUpSorted (x:xs) i j = incrLookUpSorted xs (i-1) (j-1)
