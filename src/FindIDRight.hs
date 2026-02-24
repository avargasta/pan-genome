module FindIDRight where


findIDRight :: [Int] -> [Int]
findIDRight [] = []
findIDRight (x:xs) = x : findIDRight xs