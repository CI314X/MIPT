	
pairs (x)    | length (x) <=1 = []
             | length (x) >1 = zip (func1 x) (func2 x)

func2 [] = []
func2 x =head(reverse x) : func2 (reverse(tail(reverse(tail x))))  --end

func1 [] =[]
func1 x = head x : func1 (reverse(tail(reverse(tail x))))