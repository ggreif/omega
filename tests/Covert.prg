-- Copyright (c) 2006 Portland State University.
-- This is an example program for the Omega programming language;
-- for more information, see:
--   http://www.cs.pdx.edu/~sheard/Omega/index.html
-- Research and development on Omega is supported by a grant
-- from the National Science Foundation.

-- Existenial hiding and operators on anonymous sums

data Covert :: (Nat ~> *0) ~> *0 where
  Hide :: t x -> Covert t

toNat :: Int -> Covert Nat'
toNat 0 = Hide Z
toNat n = case toNat (n-1) of Hide b -> Hide(S b)

