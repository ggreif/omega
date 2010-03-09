-- Copyright (c) 2006 Portland State University.
-- This is an example program for the Omega programming language;
-- for more information, see:
--   http://www.cs.pdx.edu/~sheard/Omega/index.html
-- Research and development on Omega is supported by a grant
-- from the National Science Foundation.

import "Library.prg" (mapP)

{-
kind Nat = Z | S Nat

data Nat' x 
  = Z where x=Z
  | exist m . S (Nat' m) where x=S m
-}

-- Ordering property.
prop LE :: Nat ~> Nat ~> *0 where
  Base_LE:: LE Z a
  Step_LE:: LE a b -> LE (S a) (S b)

-- Equality property.
prop EQ :: Nat ~> Nat ~> *0 where
  Base_EQ :: EQ Z Z
  Step_EQ :: EQ x y -> EQ (S x) (S y)

-- Inequality property.
prop NE :: Nat ~> Nat ~> *0 where
  Left_NE :: NE (S x) Z
  Right_NE :: NE Z (S x)
  Step_NE :: NE x y -> NE (S x) (S y)


-- Transitivity of ordering.
trans_LE :: LE a b -> LE b c -> LE a c
trans_LE Base_LE Base_LE = Base_LE
trans_LE Base_LE (Step_LE z) = Base_LE
trans_LE (Step_LE x) (Step_LE y) = Step_LE(trans_LE x y)

-- Transitivity of equality.
trans_EQ :: EQ a b -> EQ b c -> EQ a c
trans_EQ Base_EQ Base_EQ = Base_EQ
trans_EQ (Step_EQ x) (Step_EQ y) = Step_EQ (trans_EQ x y)

-- Commutativity of equality.
comm_EQ :: EQ a b -> EQ b a
comm_EQ Base_EQ = Base_EQ
comm_EQ (Step_EQ x) = Step_EQ (comm_EQ x)

magnitude :: Nat' x -> LE Z x
magnitude n = Base_LE

-- If a=b then a<=b.
eqToLe :: EQ a b -> LE a b
eqToLe Base_EQ = Base_LE
eqToLe (Step_EQ x) = Step_LE (eqToLe x)

-- If a<=b and b<=a, then a=b.
leToEq :: LE a b -> LE b a -> EQ a b
leToEq Base_LE Base_LE = Base_EQ
-- leEq2 Base_LE (Step_LE z) = unreachable
-- leEq2 (Step_LE z) Base_LE = unreachable
leToEq (Step_LE x) (Step_LE y) = Step_EQ (leToEq x y)

-- Tests for ordering between two naturals..
cmpare :: Nat' a -> Nat' b -> (LE a b + LE b a)
cmpare Z _ = L Base_LE
cmpare (S x) Z = R Base_LE
cmpare (S x) (S y) = mapP Step_LE Step_LE (cmpare x y)

-- Tests for equality or inequality between two naturals.
eqOrNe :: Nat' x -> Nat' y -> (EQ x y + NE x y)
eqOrNe Z Z = L Base_EQ
eqOrNe Z (S x) = R (Right_NE)
eqOrNe (S x) Z = R (Left_NE)
eqOrNe (S x) (S y) = case (eqOrNe x y) of
  (L eq) -> L (Step_EQ eq)
  (R eq) -> R (Step_NE eq)

-- Type functions on Nat.

plus :: Nat ~> Nat ~> Nat
{plus Z y} = y
{plus (S x) y} = S {plus x y}

--comm_plus :: Nat' {plus x y} -> Nat' {plus y x}
--comm_plus Z = Z
--comm_plus (S x) = S (comm_plus x)

times :: (Nat ~> Nat ~> Nat)
{times (S x) y} = {plus y {times x y}}
{times Z y} = Z
--Again, the original example included the following line, but the current
--inductiveness checker chokes on it -- this time with better reason.
--{times x #2} = {plus x x}


