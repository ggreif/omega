{-# LANGUAGE DataKinds, KindSignatures, TypeOperators
           , PolyKinds, RecursiveDo, RankNTypes #-}

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
  (~>) :: rep t' -> rep t'' -> rep t -- Morphism
  (@~) :: rep '(p', a :~> b) -> rep '(p'', a) -> rep '(p, b) -- Apply
  (.:) :: rep t' -> rep t'' -> rep t -- Inhabitation
  -- (>>=) :: 


-- Some examples
-----------------

-- let Nat = Z + Nat `Succ` Nat in List Nat

-- listOfNat = do rec let nat = con "Z" 1 + nat ~> nat
 
listOfNat :: (Type rep, forall (t :: (Pa,Ty)) . Fractional (rep t)) => rep '(PWild, Star)
listOfNat = let nat = 1 + nat ~> nat
               in nat
