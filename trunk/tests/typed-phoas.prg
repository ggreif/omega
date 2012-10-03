-- parametric HOAS (PHOAS) representation of terms
-- advocated by Chipala and B. Oliveira
--
-- Note: here we distinguish between expression, type and level
--       variables bound
--
-- See also: http://www.haskell.org/pipermail/haskell-cafe/2008-November/050768.html

data Ptm :: * ~> * ~> * ~> Nat ~> * where
  Var :: a -> Ptm a t l ll
  Lam :: (a -> Ptm a t l ll) -> Ptm a t l ll
  Lev :: (l -> Ptm a t l ll) -> Ptm a t l ll
  App :: Ptm a t l ll -> Ptm a t l ll -> Ptm a t l ll
  Star :: Nat' l -> Ptm a t (Nat' l) l
  Forall :: (t -> Ptm a t l ll) -> Ptm a t l ll
  TyVar :: t -> Ptm a t l ll
  -- 'a :: b' written as:  a `Of` b
  Of :: Ptm a t l ll -> Ptm a t l (1+ll)t -> Ptm a t l ll

data Tm :: Nat ~> * where
  Tm :: (forall a t l . Ptm a t (Nat' l) l) -> Tm ll
  Tm' :: Ptm a t (Nat' l) ll -> Tm ll


-- illegal
--
##test "not parametric"
 ill = Tm (Lam (\a -> a + 2))

##test "not parametric: expr var in level context"
 ill = Tm (Lev (\a -> App (Var a) (Var a)))

-- these are parametric
--
leg = Tm (Lam (\a -> App (Var a) (Var a)))

leg2 = Tm (Forall (\t -> TyVar t))
leg3 = Tm (Lev (\l -> Star l))

t3 :: Tm 3t
t3 = let Tm a = leg3 in Tm' a
-- t3' = let Tm' (Lev a) = t3 in a 3v  -- MAY I USE IT THIS MANNER?
