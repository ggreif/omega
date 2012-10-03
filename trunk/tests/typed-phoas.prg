-- parametric HOAS (PHOAS) representation of terms
-- advocated by Chipala and B. Oliveira
--

data Ptm :: * ~> * ~> * where
  Var :: a -> Ptm a l
  Lam :: (a -> Ptm a l) -> Ptm a l
  Lev :: (l -> Ptm  a l) -> Ptm a l
  App :: Ptm a l -> Ptm a l -> Ptm a l

data Tm = Tm (forall a l . Ptm a l)


-- illegal
--
##test "not parametric"
 ill = Tm (Lam (\a -> a + 2))

##test "not parametric: expr var in level context"
 ill = Tm (Lev (\a -> App (Var a) (Var a)))

-- this is parametric
--
leg = Tm (Lam (\a -> App (Var a) (Var a)))

