remove :: [a] -> Int -> Int -> [a]
remove (x:xs) y z | length (x:xs)<z = error "Wrong numbers"
				  | y>z = error "Wrong numbers"
				  | y==0 = error "y=0"
				  | otherwise = func(take z (x:xs)) y
				  
func :: [a] -> Int -> [a]				  
func (x:xs) y | y==1 = x:xs
              | y/=1 = func xs (y-1)
			  
	  