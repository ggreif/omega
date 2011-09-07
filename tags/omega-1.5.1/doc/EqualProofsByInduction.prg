--\begin{verbatim}
----------------------------------------------------
-- This file depends upon the predefined GADTs
-- kind Nat = Z | S Nat 
-- 
-- prop Nat' :: Nat ~> *0 where
--   Z:: Nat' Z
--   S:: forall (a:: Nat) . Nat' a -> Nat' (S a)
-- 
-- data Equal :: forall (a:: *1) . a ~> a ~> *0 where
--   Eq:: forall (b:: *1) (x:: b) . Equal x x

---------------------------------------------------
-- define plus as a recursive type-function

plus:: Nat ~> Nat ~> Nat
{plus Z m} = m
{plus (S n) m} = S {plus n m}  -- deriving Relation Plus

---------------------------------------------------
-- plusZ is proved by induction. Note how we use
-- a recursive call "plusZ m" to produce the induction
-- hypothesis, and how we use the "theorem" decl.

plusZ :: Nat' n -> Equal {plus n Z} n
plusZ Z = Eq
plusZ (x@(S m)) = Eq
  where theorem indHyp = plusZ m

---------------------------------------------------
-- plusS is proved in a manner similar to plusZ

plusS :: Nat' n -> Equal {plus n (S m)} (S{plus n m})
plusS Z  = Eq
plusS (S x)  = Eq
  where theorem ih = plusS x
        
---------------------------------------------------
-- we use both induction, and plusZ and plusS to
-- show that plus commutes.

plusCommutes :: Nat' n -> Nat' m -> Equal {plus n m} {plus m n}
plusCommutes Z m = Eq
   where theorem lemma = plusZ m
plusCommutes (S x) m = Eq
   where theorem plusS,
                 indHyp = plusCommutes x m
         
-------------------------------------------------
-- We can prove similar results, first by defining
-- plus as a ternary relation "Plus". This 
-- relation is a witness type.

data Plus:: Nat ~> Nat ~> Nat ~> *0 where
  Plus0 :: Plus Z m m
  Plus1 :: Plus n m c -> Plus (S n) m (S c)

-------------------------------------------------
-- the relational analog to plusS

pluS:: Plus a b c -> Plus a (S b) (S c)
pluS Plus0 = Plus0
pluS (Plus1 p) = Plus1(pluS p)


------------------------------------------------
-- the relational analog to plusCommutes

plusCom:: Nat' b -> Plus a b c -> Plus b a c
plusCom Z Plus0 = Plus0
plusCom (S n) Plus0 = Plus1(plusCom n Plus0)
plusCom Z (Plus1 p) = pluS(plusCom Z p)
plusCom (S n) (Plus1 p) = pluS(plusCom (S n) p)

--------------------------------------------------
-- To show that the two approaches are equivalent,
-- we show that we can convert or translate from
-- each to the other.

trans:: Plus a b c -> Equal {plus a b} c
trans Plus0 = Eq
trans (Plus1 p) =  Eq
  where theorem indHyp = trans p

transInv :: Nat' a -> Equal {plus a b} c -> Plus a b c
transInv Z Eq = Plus0
transInv (x@(S n)) (p@Eq) = Plus1(transInv n Eq)

---------------------------------------------------
-- Show that the relation Plus is functional, i.e.
-- if we know the first two arguments, we can 
-- determine the third.

funcDepend:: (Plus a b c,Plus a b d) -> Equal c d
funcDepend (Plus0,Plus0) = Eq
funcDepend (Plus0,Plus1 p) = unreachable
funcDepend (Plus1 p,Plus0) = unreachable
funcDepend (Plus1 p,Plus1 q) = 
   case funcDepend(p,q) of
     Eq -> Eq

--\end{verbatim} 
