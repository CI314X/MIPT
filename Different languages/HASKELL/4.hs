
rev (x:xs) | length (x:xs)==2 =  xs ++ [x]
           | length (x:xs)<2  = (x:xs)
		   | length (x:xs)>2  = f xs ++ body xs ++ [x]		   

f (x:xs) | length (x:xs)==1 = [x]                       -- last element
         | length (x:xs)/=1 = f(xs)
		 
body (x:xs) | length (x:xs)/=1 = x : body xs
            | length (x:xs)==1 = []