-- Copyright (c) 2006 Portland State University.
-- This is an example program for the Omega programming language;
-- for more information, see:
--   http://www.cs.pdx.edu/~sheard/Omega/index.html
-- Research and development on Omega is supported by a grant
-- from the National Science Foundation.

-- Existential hiding and operators on anonymous sums

data Covert :: (a ~> *0) ~> *0 where
  Hide :: t x -> Covert t
 deriving Item(cv)

-- conventional (ADT) syntax would be
-- data Covert f = exists x . Hide (f x) deriving Item(cv)

toNat :: Int -> Covert Nat'
toNat 0 = Hide Z
toNat n = case toNat (n-1) of Hide b -> Hide(S b)

