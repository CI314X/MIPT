remove2 :: [a] -> Int -> Int -> [a]
remove2 (x:xs) y z | length (x:xs)<z = error "Wrong numbers"
				   | y>z = error "Wrong numbers"
				   | y==0 = error "y=0"
				   | otherwise = func1 (x:xs) y z
				   
func1 :: [a] -> Int -> Int -> [a]
func1 (x:xs) y z | y==1	= 			   
				 | y 