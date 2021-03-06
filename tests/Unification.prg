-- This extended example is an Omega port of Conor McBride's First Order Unification by Structural Recursion
-- adapted to the recent Omega dialect.
-- From the paper "GADTs + Extensible Kinds = Dependent Programming"

-------- MAYBE MONAD --------------------------------
return x = Just x
fail s = Nothing
bind Nothing g = Nothing
bind (Just x) g = g x

liftM :: (a -> b) -> Maybe a -> Maybe b
liftM2 :: (a -> b -> c) -> Maybe a -> Maybe b -> Maybe c
liftM f ma = do { a <- ma; return (f a) }
liftM2 f ma mb = do { a <- ma; b <- mb; return (f a b) }

------- FINITE (VARIABLE) SETS & TERMS --------------
data Fin :: Nat ~> *0 where
  Fz :: Fin (S m)
  Fs :: Fin m -> Fin (S m)
 deriving Nat(f)

data Term n = Var (Fin n) | Leaf | Fork (Term n) (Term n)
  deriving syntax(t) Unit(Leaf) Item(Var) Pair(Fork)

------- SUBSTITUTIONS -------------------------------
rename2sub :: (Fin m -> Fin n) -> Fin m -> Term n
rename2sub f i = Var (f i)

subst :: (Fin m -> Term n) -> Term m -> Term n
subst sub (Var x) = sub x
subst sub Leaf = Leaf
subst sub (Fork s t) = Fork(subst sub s)(subst sub t)

compose :: (Fin m -> Term n) -> (Fin l -> Term m) -> (Fin l -> Term n)
compose f g i = subst f (g i)

------- OCCURS CHECK --------------------------------
thick :: Nat' n -> Fin (S n) -> Fin (S n) -> Maybe (Fin n)
thick n (Fz) (Fz) = Nothing
thick n (Fz) (Fs y) = Just y
thick (S n) (Fs x) (Fz) = Just Fz
thick (S n) (Fs x) (Fs y) = liftM Fs (thick n x y)

chk :: Nat' n -> Fin (S n) -> Term (S n) -> Maybe (Term n)
chk n x (Var y) = liftM Var (thick n x y)
chk n x (Leaf) = Just Leaf
chk n x (Fork s t) = liftM2 Fork(chk n x s)(chk n x t)

for :: Nat' n -> Term n -> Fin (S n) -> Fin (S n) -> Term n
for n t' x y = case thick n x y of
               Just y' -> Var y'
               Nothing -> t'

-----------------------------------------------------
-- substitution lists
data AList :: Nat ~> Nat ~> *0 where
  Anil :: AList n n
  Asnoc :: AList m' n -> Term m' -> Fin (S m') -> AList (S m') n
 deriving LeftRecord(a)

sub :: Nat' m -> AList m n -> (Fin m -> Term n)
sub _ {}a = Var
sub (S n) {s; t=x}a = compose (sub n s) (for n t x)

cat :: AList m n -> AList l m -> AList l n
cat xs {}a = xs
cat xs {ys; t=x}a = {cat xs ys; t=x}a

data SomeSub m = exists n . SomeSub (Nat' n) (AList m n)
asnoc :: SomeSub m -> Term m -> Fin (S m) -> SomeSub (S m)
asnoc (SomeSub m s) t x = SomeSub m {s; t=x}a

-----------------------------------------------------
-- unification
mgu :: Nat' m -> Term m -> Term m -> Maybe (SomeSub m)
mgu m s t = amgu m s t (SomeSub m {}a)
  where amgu :: Nat' m -> Term m -> Term m -> SomeSub m -> Maybe (SomeSub m)
        amgu m (Leaf) (Leaf) acc = Just acc
        amgu m (Leaf) (Fork s t) acc = Nothing
        amgu m (Fork s t) (Leaf) acc = Nothing
        amgu m (Fork s1 t1) (Fork s2 t2) acc =
             do { acc <- amgu m s1 t1 acc; amgu m s2 t2 acc }
        amgu m (Var x) (Var y) (SomeSub _ {}a) = Just (flexFlex m x y)
        amgu m (Var x) t (SomeSub _ {}a) = flexRigid m x t
        amgu m s (Var x) (SomeSub _ {}a) = flexRigid m x s
        amgu (S m) s t (SomeSub n {sub; r=z}a) =
             do sub <- amgu m (subst (for m r z) s) (subst (for m r z) t) (SomeSub n sub)
                return (asnoc sub r z)

flexFlex :: Nat' m -> Fin m -> Fin m -> SomeSub m
flexFlex (S m) x y = case thick m x y of
                     Just y' -> SomeSub m {Var y'=x}a
                     Nothing -> SomeSub (S m) {}a

flexRigid :: Nat' m -> Fin m -> Term m -> Maybe (SomeSub m)
flexRigid (S m) x t = do
                      t' <- chk m x t
                      return (SomeSub m {t'=x}a)

