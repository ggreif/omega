-- Copyright (c) 2006 Portland State University.
-- This is an example program for the Omega programming language;
-- for more information, see:
--   http://www.cs.pdx.edu/~sheard/Omega/index.html
-- Research and development on Omega is supported by a grant
-- from the National Science Foundation.

-- Library routines useful in other examples.

mapP :: (a -> b) -> (c -> d) -> (a+c) -> (b+d)
mapP f g (L x) = L(f x)
mapP f g (R x) = R(g x)        

unP ::  (a+a) -> a
unP (L x) = x
unP (R x) = x

map f [] = []
map f (x:xs) = f x : map f xs
