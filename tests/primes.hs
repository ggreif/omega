
primes = 2 : 3 : lazy (filter isPrime [5..])
  where isPrime n = not $ any (`divides` n) $ takeWhile ((<= n) . \n -> n * n) primes
        divides m n = n `mod` m == 0
	lazy = id
