-- parametric HOAS (PHOAS) representation of terms
-- advocated by Chipala and B. Oliveira
--

data Ptm :: * ~> * ~> * ~> * where
  Var :: a -> Ptm a t l
  Lam :: (a -> Ptm a t l) -> Ptm a t l
  Lev :: (l -> Ptm a t l) -> Ptm a t l
  App :: Ptm a t l -> Ptm a t l -> Ptm a t l
  Star :: l -> Ptm a t l
  Forall :: (t -> Ptm a t l) -> Ptm a t l
  TyVar :: t -> Ptm a t l

data Tm = Tm (forall a t l . Ptm a t (Nat' l))


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
