{-# LANGUAGE DataKinds, KindSignatures, TypeOperators
           , PolyKinds, RecursiveDo, RankNTypes
           , FlexibleInstances #-}

-- This is just a small playground which will (hopefully) be absorbed
-- in finally-predicative.hs as soon as it is sufficiently polished.

-- Note: we could use pi-types here (or generalized lambdas),
--       but I'd rather try to follow the "patterned type" idea.

-- universe of patterns
data {-kind-} Pa = PWild | C Ty

-- universe of types
data {-kind-} Ty = Star | Ty :~> Ty

class Type (rep :: (Pa,Ty) -> *) where
  star :: rep '(C Star, Star)
  --(~>) :: rep '(p, a) -> rep '(q, b) -> rep '(PWild, a :~> b) -- Morphism
  --(~>) :: rep '(p, a) -> rep '(q, b) -> rep '(C (a :~> b), Star) -- Morphism
  (~>) :: rep '(p, a) -> rep '(q, b) -> rep '(r, Star) -- Morphism
  (@~) :: rep '(p', a :~> b) -> rep '(p'', a) -> rep '(p, b) -- Apply
  (.:) :: rep t' -> rep t'' -> rep t -- Inhabitation
  plus :: rep t' -> rep t'' -> rep t -- Sum
  zero :: rep t
  -- (>>=) :: 


-- Some examples
-----------------

-- let Nat = Z + Nat `Succ` Nat in List Nat

-- listOfNat = do rec let nat = con "Z" 1 + nat ~> nat

--instance Type rep => Num (forall t . rep t)
--  where (+) = plus

--listOfNat :: (Type rep, forall (t :: (Pa,Ty)) . Fractional (rep t)) => rep '(PWild, Star)
listOfNat :: Type rep => rep '(p, Star)
listOfNat = let nat = zero `plus` nat ~> nat
               in \_ -> nat -- this is #9301

high :: Type rep => rep '(p, Star)
high = star ~> star
