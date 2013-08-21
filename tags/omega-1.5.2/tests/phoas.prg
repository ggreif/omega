-- parametric HOAS (PHOAS) representation of terms
-- advocated by Chipala and B. Oliveira
--

data Ptm a = Var a
           | Lam (a -> Ptm a)
           | App (Ptm a) (Ptm a)

data Tm = Tm (forall a . Ptm a)


-- illegal
--
##test "not parametric"
 ill = Tm (Lam (\a -> a + 2))

-- this is parametric
--
leg = Tm (Lam (\a -> App (Var a) (Var a)))

