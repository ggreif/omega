{-# LANGUAGE ViewPatterns #-}

{- The spirit of guarded recursion is that we can only
   re-enter the recursion with a smaller value.
   Can we enforce this with view patterns and a type system that
   tracks effective refinement types?
-}

import Control.Arrow

data Nat = Z | S Nat deriving Show

five = S (S (S (S (S Z))))
six = S five
eight = fib six
twentyOne = fib eight

-- Here comes the challenge: we cannot use the
-- induction hypothesis on the right hand sides
-- of our equations, only in the patterns!
-- (And not on top-level!)

plus m Z = m
plus m (S (plus m -> sum)) = S sum
---         |
---         +--> :: Nat -> (S effective ° Nat) -> Nat

fib :: Nat -> Nat
fib zero@Z = zero
fib one@(S Z) = one
fib (S (fib&&&id -> (f, S (fib -> g)))) = f `plus` g
---      |                  |
---      |                  +--> :: (S (S effective) ° Nat) -> Nat
---      |
---      +--> :: (S effective ° Nat) -> Nat
