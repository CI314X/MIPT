primes:: Int -> [Int]
primes n = [x | x <- [2..n], is_prime x]
isPrime_help :: Int -> Int -> Bool
isPrime_help a b |b > 1 = if mod a b /= 0 then  isPrime_help a (b - 1)
			else False
		 |otherwise = True
is_prime::Int -> Bool
is_prime a = isPrime_help a (a - 1)