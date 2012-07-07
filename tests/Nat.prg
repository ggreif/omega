-- Copyright (c) 2006 Portland State University.
-- This is an example program for the Omega programming language;
-- for more information, see:
--   http://www.cs.pdx.edu/~sheard/Omega/index.html
-- Research and development on Omega is supported by a grant
-- from the National Science Foundation.

-- Ordering property.
prop LE :: Nat ~> Nat ~> *0 where
  Base_LE:: LE Z a
  Step_LE:: LE a b -> LE (S a) (S b)

-- Equality property.
prop EQNat:: Nat ~> Nat ~> *0 where
  Base_EQ :: EQNat Z Z
  Step_EQ :: EQNat x y -> EQNat(S x) (S y)

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
trans_EQ :: EQNat a b -> EQNat b c -> EQNat a c
trans_EQ Base_EQ Base_EQ = Base_EQ
trans_EQ (Step_EQ x) (Step_EQ y) = Step_EQ (trans_EQ x y)

-- Commutativity of equality.
comm_EQ :: EQNat a b -> EQNat b a
comm_EQ Base_EQ = Base_EQ
comm_EQ (Step_EQ x) = Step_EQ (comm_EQ x)

magnitude :: Nat' x -> LE Z x
magnitude n = Base_LE

-- If a=b then a<=b.
eqToLe :: EQNat a b -> LE a b
eqToLe Base_EQ = Base_LE
eqToLe (Step_EQ x) = Step_LE (eqToLe x)

-- If a<=b and b<=a, then a=b.
leToEq :: LE a b -> LE b a -> EQNat a b
leToEq Base_LE Base_LE = Base_EQ
-- leEq2 Base_LE (Step_LE z) = unreachable
-- leEq2 (Step_LE z) Base_LE = unreachable
leToEq (Step_LE x) (Step_LE y) = Step_EQ (leToEq x y)

{-
-- Tests for ordering between two naturals..
compareN :: Nat' a -> Nat' b -> (LE a b + LE b a)
compareN Z _ = L Base_LE
compareN (S x) Z = R Base_LE
compareN (S x) (S y) = mapP Step_LE Step_LE (compareN x y)
-}

-- Tests for equality or inequality between two naturals.
eqOrNe :: Nat' x -> Nat' y -> (EQNat x y + NE x y)
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


data LT:: Nat ~> Nat ~> *0  where
  BLT:: LT Z (S a)
  SLT:: LT a b -> LT (S a) (S b)
  
data LT' :: Nat ~> Nat ~> *0  where
  BLT':: LT' a (S a)
  SLT':: LT' a b -> LT' a (S b)

h:: Nat' m -> LT' Z (S m)
h Z = BLT'
h (S m) = SLT'(h m)

k:: Nat' b -> LT' a b -> LT' (S a) (S b)
k Z BLT' = unreachable
k Z (SLT' p) = unreachable
k (S m) BLT' = BLT'
k (S m) (SLT' p) = SLT'(k m p)

m:: Nat' b -> LT a b -> LT a (S b)
m Z BLT = unreachable
m Z (SLT p) = unreachable
m (S n) BLT = BLT
m (S n) (SLT p) = SLT(m n p)

f:: Nat' (S m) -> LT n (S m) -> LT' n (S m)
f Z     BLT = unreachable 
f Z (SLT p) = unreachable
f (S Z) BLT = h Z
f (S (S n)) (SLT p) = k (S n) (f (S n) p)

g:: Nat' (S m) -> LT' n (S m) -> LT n (S m)
g Z BLT' = unreachable
g Z (SLT' p) = unreachable
g (S Z) BLT' = BLT
g (S (S n)) (SLT' p) = m (S n) (g (S n) p)
  