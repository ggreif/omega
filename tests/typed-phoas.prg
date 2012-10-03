-- parametric HOAS (PHOAS) representation of terms
-- advocated by Chipala and B. Oliveira
--

data Ptm :: * ~> * ~> * ~> Nat ~> * where
  Var :: a -> Ptm a t l ll
  Lam :: (a -> Ptm a t l ll) -> Ptm a t l ll
  Lev :: (l -> Ptm a t l ll) -> Ptm a t l ll
  App :: Ptm a t l ll -> Ptm a t l ll -> Ptm a t l ll
  Star :: Nat' l -> Ptm a t (Nat' l) ll
  Forall :: (t -> Ptm a t l ll) -> Ptm a t l ll
  TyVar :: t -> Ptm a t l ll

data Tm :: Nat ~> * where
  Tm :: (forall a t l . Ptm a t (Nat' l) ll) -> Tm ll


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
