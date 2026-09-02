{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ infix :               @-}
module Data.RList where

{-@ type SortedList a = [a]<{\i j -> i <= j}>  @-} -- Expressing sortedness using abstract refinements  

{-@ sort :: Ord a => xs:[a] -> {v:SortedList a | len v == len xs} @-}
sort :: Ord a => [a] -> [a]
sort []     = []
sort (x:xs) = insert x (sort xs)

{-@ insert :: Ord a => x:a -> xs:SortedList a -> {v:SortedList a | len v == len xs + 1} @-}
insert :: Ord a => a -> [a] -> [a]
insert x [] = [x]
insert x (y:ys)
  | x <= y    = x : y : ys
  | otherwise = y : insert x ys

{-@ iterateN :: (a -> a) -> n:Nat -> a -> {v:[a] | len v == n} @-}
iterateN :: (a -> a) -> Int -> a -> [a]
iterateN _ 0 _ = []
iterateN f n x = x : iterateN f (n-1) (f x)

{-@ elemIndexNat :: Eq a => a -> xs:[a] -> Maybe {v:Nat | v < len xs} @-}
elemIndexNat :: Eq a => a -> [a] -> Maybe Int
elemIndexNat _ [] = Nothing
elemIndexNat x (y:ys)
    | x == y    = Just 0
    | otherwise = case elemIndexNat x ys of
                    Just n  -> Just (n + 1)
                    Nothing -> Nothing 

{-@ reflect index @-}
{-@ index :: xs:[a] -> {v:Int | 0 <= v && v < len xs} -> a @-}
index :: [a] -> Int -> a
index (x:_) 0  = x
index (_:xs) n = index xs (n-1)

{-@ lookupSorted :: x:a -> xs:SortedList {y:a | x <= y} -> i:{Nat | i < len xs + 1} 
                 -> { x <= index (x:xs) i } @-} -- Ensures that if x is less than or equal to the head of the list, then it is less than or equal to the element at index i in the list
lookupSorted :: Ord a => a -> [a] -> Int -> ()
lookupSorted _ [] _ = ()
lookupSorted _ (y:ys) i
    | i == 0    = ()
    | otherwise = lookupSorted y ys (i-1) 

{-@ incrLookUpSorted :: xs: SortedList a  
                     -> i:Nat
                     -> j:{Nat | i <= j && j < len xs}
                     -> { index xs i <= index xs j } @-} -- Monotony of lists
incrLookUpSorted :: Ord a => [a] -> Int -> Int -> ()
incrLookUpSorted (x:xs) 0 j =
    if j == 0 then () else lookupSorted x xs j 
incrLookUpSorted (_:_) _ 0 = ()
incrLookUpSorted (_:xs) i j = incrLookUpSorted xs (i-1) (j-1)
