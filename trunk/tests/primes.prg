import "../src/LangPrelude.prg"

primes = 2 : 3 : lazy (filter isPrime from5)

isPrime n = not (any (\m -> n `mod` m == 0) $ takeWhile ((\m -> m <= n) . (\n -> n * n)) primes)

from5 = 5 : lazy (lmap (\n -> n + 1) from5)

lmap f [] = []
lmap f [i;is] = [f i; lazy (lmap f is)]

any p [] = False
any p [i;is] | p i = True
             | otherwise = any p is

takeWhile _ []                 =  []
takeWhile p [x;xs] | p x       =  [x; takeWhile p xs]
                   | otherwise =  []

filter _ []      = []
filter p [x;xs]
     | p x       = [x; lazy (filter p xs)]
     | otherwise = filter p xs

take 0 _ = []
take n [i;is] = [i; take (n - 1) is]
