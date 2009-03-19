
data Var :: *0 ~> *0 ~> *0 where
   Zv :: Var ((d,t)) t
   Sv :: (Var d t) -> Var ((d,t2)) t

data Exp :: *0 ~> *0 ~> *0 where
   V :: (Var e t) -> Exp e t
   Abs :: (Exp ((e,t1)) t2) -> Exp e (t1 -> t2)
   App :: (Exp e (t1 -> t)) -> (Exp e t) -> Exp e t
   Pair :: (Exp e t1) -> (Exp e t2) -> Exp e ((t1,t2))
   Const :: t -> Exp e t

data Subst :: *0 ~> *0 ~> *0 where
   IdSub :: Subst delta delta
   Shift :: Subst ((delta,t1)) delta
   Comp :: (Subst d delta) -> (Subst gamma d) -> Subst gamma delta
   Cons :: (Exp gamma t1) -> (Subst gamma d) -> Subst gamma ((d,t1))


subst :: Subst e delta -> Exp delta t -> Exp e t
subst s e = 
 case (simplSub s, e) of 
     (IdSub, e) -> e
     (r,V v) -> substVar  r v
     (r,App e1 e2) -> App (subst r e1) (subst r e2)
     (r,Abs e) -> Abs (subst (Cons (V Zv) (Comp r Shift)) e)
     (r,Pair e1 e2) -> Pair (subst r e1) (subst r e2)
     (r,Const x) -> Const x



substVar :: Subst e delta -> Var delta t -> Exp e t
substVar s Zv = 
  case simplSub s of 
      IdSub -> V Zv
      Cons m t -> m
      Comp r t -> subst t (substVar r Zv)
      Shift -> V (Sv Zv)
substVar  s (Sv v) = 
  case simplSub s of 
        IdSub -> V (Sv v)
        Cons m t -> substVar t v
        Comp r t -> subst t (substVar r (Sv v))
        Shift -> V (Sv (Sv v))


simplSub :: Subst e1 e2 -> Subst e1 e2
simplSub (Comp r s) = 
  case (simplSub r, simplSub s) of 
    (Comp r s,t) -> simplSub (Comp r (Comp s t))
    (Cons m s,t) -> Cons (subst t m) (simplSub (Comp s t))
    (IdSub, s) -> s
    (s, IdSub) -> s
    (Shift, Cons m s) -> s
    (a,b) -> Comp a b
simplSub (Cons e s) = 
  case (e,simplSub s) of 
     (V Zv, Shift) -> IdSub
     (e,r)        -> (Cons e r)
simplSub x = x     



e1 = Pair (V Zv) (Pair (V (Sv Zv)) (V (Sv (Sv Zv))))
s1 = Cons (Const 1) (Cons (Const 2) (Cons (Const 3) IdSub))
e2 = Abs e1
