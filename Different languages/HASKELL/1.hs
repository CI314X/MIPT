isEmpty :: [Int] -> Bool
isEmpty [] = False
isEmpty _ = True

gpls :: [Int]-> [Int]
gpls (x:xs) |isEmpty xs = [x] ++ gpls xs
	      |otherwise = []

delLast :: [Int] -> [Int]
delLast [] = error "oshibka"
delLast (x:xs) |isEmpty xs = [x] ++ gpls xs
	       |otherwise = error "oshibka"

makeSpis :: [Int] -> [Int]
makeSpis (x:xs) = delLast xs

func :: [Int] -> Int -> [Int]
func (x:xs) a |isEmpty xs = [a] ++ gpls xs
	      |otherwise = [x] ++ [a]

gpl :: [Int] -> [Int]
gpl [] = error "oshibka"
gpl (x:xs) |isEmpty xs = [x] ++ gpls xs
	   |otherwise = error "oshibka"