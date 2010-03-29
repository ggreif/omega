data ObjType:: *1 where
 ArrT:: ObjType ~> ObjType ~> ObjType
 IntT:: ObjType
 
data Rel:: ObjType ~> *0 ~> *0 where
 IntR:: Rel IntT Int
 IntTo:: Rel b s -> Rel (ArrT IntT b) (Int -> s) 
   -- First order functions only as constants

data Mode:: *1 where
 Exp:: Mode
 Val:: Mode

data E:: Mode ~> Row Tag ObjType ~> ObjType ~> *0  where
  Const:: Rel a b -> b -> E Val env a
  Var  :: Label s -> E Val (RCons s t env) t
  Shift:: E m env t -> E m (RCons s q env) t
  Lam  :: Label a -> E m (RCons a s env) t -> E Val env (ArrT s t)
  App  :: E m1 env (ArrT s t) -> E m2 env s -> E Exp env t

exp1 = Lam `f (Lam `y (App (Shift(Var `f)) (Var `y)))
int n = Const IntR n
oper x = Const (IntTo (IntTo IntR)) x

one = int 1
plus = oper (+)

-------------------------------------------------------
-- substitutions and substitute functions

data Sub:: Row Tag ObjType ~> Row Tag ObjType ~> *0 where
  Id:: Sub r r
  Bind:: Label t -> E m r2 x -> Sub r r2 -> Sub (RCons t x r) r2
  Push:: Sub r1 r2 -> Sub (RCons a b r1) (RCons a b r2)

subst:: E m1 r t -> Sub r s -> exists m2 . E m2 s t
subst t Id = Ex t
subst (Const r c) sub = Ex (Const r c)
subst (Var v) (Bind u e r) = Ex e
subst (Var v) (Push sub) = Ex (Var v)
subst (Shift e) (Bind _ _ r) = subst e r
subst (Shift e) (Push sub) = 
  case subst e sub of {Ex a -> Ex(Shift a)}
subst (App f x) sub = 
  case (subst f sub,subst x sub) of
    (Ex g,Ex y) -> Ex(App g y)
subst (Lam v x) sub = 
  case subst x (Push sub) of
    (Ex body) -> Ex(Lam v body)

-----------------------------------------
-- Distingushing values from expressions

data Mode':: Mode ~> *0 where
  Exp':: Mode' Exp
  Val':: Mode' Val
  
mode :: E m e t -> Mode' m
mode (Lam v body) = Val'
mode (Var v) = Val'
mode (Const r v) = Val'
mode (Shift e) = mode e
mode (App _ _) = Exp' 

type Closed = RNil
    
onestep :: E m Closed t -> (E Exp Closed t + E Val Closed t)
onestep (Var v)      = unreachable
onestep (Shift e)    = unreachable
onestep (Lam v body) = R (Lam v body)
onestep (Const r v)  = R(Const r v)
onestep (App e1 e2)  =
  case (mode e1,mode e2) of
    (Exp',_) -> 
      case onestep e1 of
        L e -> L(App e e2)
        R v -> L(App v e2)
    (Val',Exp') ->
      case onestep e2 of
        L e -> L(App e1 e)
        R v -> L(App e1 v)
    (Val',Val') -> rule e1 e2

rule::  E Val Closed (ArrT a b) -> 
        E Val Closed a -> 
        (E Exp Closed b + E Val Closed b)
rule (Var _)   _ = unreachable
rule (Shift _) _ = unreachable
rule (App _ _) _ = unreachable        
rule (Lam x body) v =
  let (Ex term) = subst body (Bind x v Id)
  in case mode term of
       Exp' -> L term
       Val' -> R term
rule (Const IntR _)      _                   = unreachable
rule (Const (IntTo b) _) (Var _)             = unreachable
rule (Const (IntTo b) _) (Shift _)           = unreachable
rule (Const (IntTo b) _) (App _ _)           = unreachable 
rule (Const (IntTo b) f) (Lam x body)        = unreachable
rule (Const (IntTo b) f) (Const (IntTo _) x) = unreachable
rule (Const (IntTo b) f) (Const IntR x)      = R(Const b (f x)) 

------------------------------------------------
same :: Rel a b -> Rel a d -> Equal b d
same IntR IntR = Eq
same (IntTo y) (IntTo t) = 
  case (same y t) of
    (Eq) -> Eq
same IntR (IntTo _) = unreachable 
same (IntTo _) IntR = unreachable 
 

----------------------------------------
mon = Monad return bind fail
 where return x = R x
       fail s = L s
       bind (R x) f = f x
       bind (L s) f = L s

monad mon
type M x = (String + x)

---------------------------------

data Rep:: ObjType ~> *0 where
 I:: Rep IntT
 Ar:: Rep a -> Rep b -> Rep (ArrT a b)

compareRep :: Rep a -> Rep b -> (String + Equal a b)
compareRep I I = R Eq
compareRep (Ar x y) (Ar s t) =
  do { Eq <- compareRep x s
     ; Eq <- compareRep y t
     ; R Eq}
compareRep I (Ar x y) = L "I /= (Ar _ _)"
compareRep (Ar x y) I = L "(Ar _ _) /= I"

data Env:: Row Tag ObjType ~> *0 where
   Enil:: Env RNil
   Econs:: Label t -> (String,Rep x) -> Env e -> Env (RCons t x e)
 deriving Record(e)
 
data Term:: *0 where
  C:: Int -> Term
  Ab:: String -> Rep a -> Term -> Term
  Ap:: Term -> Term -> Term
  V:: String -> Term
  
lookup:: String -> Env e -> (String + exists t m .(E m e t,Rep t))
lookup name Enil = fail ("Name not found: "++name)
lookup name {l=(s,t);rs}e | eqStr name s = R(Ex(Var l,t))
lookup name {l=(s,t);rs}e =
  do { Ex(v,t) <- lookup name rs
     ; R(Ex(Shift v,t)) }
     
tc:: Term -> Env e -> (String + exists t m . (E m e t,Rep t))
tc (V s) env = lookup s env
tc (Ap f x) env = 
  do { Ex(f',ft) <- tc f env
     ; Ex(x',xt) <- tc x env
     ; case ft of 
        (Ar a b) -> 
           do { Eq <- compareRep a xt
              ; R(Ex(App f' x',b)) }
        _ -> fail "Non fun in Ap" }
tc (Ab s t body) env = 
  do { let (HideLabel l) = newLabel s
     ; Ex(body',et) <- tc body {l=(s,t); env}e
     ; R(Ex(Lam l body',Ar t et)) }
tc (C n) env = R(Ex(Const IntR n,I))


good = Ab "f" (Ar I I) (Ab "x" I (Ap (V "f") (V "x")))
bad1 = Ab "f" (Ar I I) (Ab "x" I (Ap (V "g") (V "x")))

bad2 = Ab "f" (Ar I I) (Ab "x" I (Ap (V "x") (V "f")))
