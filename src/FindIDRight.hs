module FindIDRight where


findIDRight :: [Int] -> [Int]
findIDRight [] = []
findIDRight (x:xs) = x : findIDRight xs


{-@ foo :: {v:Int | v /= 0} -> Int @-}
foo :: Int -> Int 
foo x = 42 `div` x