-----------------------------------------
-- We need have things at 3 levels

-- Level 0 -  Exp' Exp env t
-- Level 1 -  Exp env t
-- Level 2 -  Env, Typ, etc

-- So we need names at three levels 

data Name :: *2 where
   A:: Name
   B:: Name
   C:: Name
   D:: Name
   
data Sym :: Name ~> *1 where
   A1 :: Sym A
   B1 :: Sym B
   C1 :: Sym C
   D1 :: Sym D
   
data Sym' :: Sym a ~> Name ~> *0 where
   A0:: Sym' A1 A
   B0:: Sym' B1 B
   C0:: Sym' C1 C
   D0:: Sym' D1 D

-------------------------------------------------
-- Types

data Typ:: *2 where
   NatT:: Typ
   ArrT:: Typ ~> Typ ~> Typ

-------------------------------------------------
-- Environments map names to types

data Env:: *2 where
   Closed :: Env
   ConsEnv :: Name ~> Typ ~> Env ~> Env
 deriving Record(e)

---------------------------------------------
-- Expressions at level 1.

data Exp:: Env ~> Typ ~> *1 where
  Z1:: Exp env NatT
  S1:: Exp env NatT ~> Exp env NatT
  If1:: Exp env NatT ~> 
        Exp env t ~> 
        Exp env (ArrT NatT t) ~>
        Exp env t
  App1  :: Exp env (ArrT s t) ~> Exp env s ~> Exp env t
  Var1  :: Sym s ~> Exp {s=t; env}e t
  Sh1:: Exp env t ~> Exp {s=q;env}e t
  Lam1  :: Sym f ~> Sym a ~> 
           Exp {a=s,f=ArrT s t; env}e t ~>
           Exp env (ArrT s t)
            
-------------------------------------------------------
-- Substitution, A Sub maps names to terms (at Level 1)

data Sub:: Env ~> Env ~> *1 where
  Id:: Sub env env
  Bnd:: Sym a ~> 
        Exp env t ~> 
        Sub r1 r2 ~>
        Sub (ConsEnv a t r1) r2
  Push:: Sub r1 r2 ~> Sub (ConsEnv a t r1) (ConsEnv a t r2)        

-- DeBruijn index style

subst:: Sub a b ~> Exp a t ~> Exp b t
{subst Id x} = x
{subst (Bnd s x env) (Var1 s)} = x
{subst (Bnd s x env) (Sh1 x)} = x
{subst (Bnd s x env) Z1} = Z1
{subst (Bnd s x env) (S1 n)} = {subst (Bnd s x env) n} 
{subst (Bnd s x env) (App1 f y)} = 
   App1 {subst (Bnd s x env) f} {subst (Bnd s x env) y}
{subst (Bnd s x env) (If1 tst th el)} = 
  If1 {subst (Bnd s x env) tst}
      {subst (Bnd s x env) th}
      {subst (Bnd s x env) el}
{subst (Bnd s x env) (Lam1 f y bod)} = 
  Lam1 f y {subst (Push (Push (Bnd s x env))) bod}
{subst (Push r) (Var1 s)} = (Var1 s)
{subst (Push r) (Sh1 x)} = Sh1 {subst r x}
{subst (Push r) Z1} = Z1
{subst (Push r) (S1 n)} = {subst (Push r) n} 
{subst (Push r) (App1 f y)} = 
   App1 {subst (Push r) f} {subst (Push r) y}
{subst (Push r) (If1 tst th el)} = 
  If1 {subst (Push r) tst}
      {subst (Push r) th}
      {subst (Push r) el}
{subst (Push r) (Lam1 f y bod)} = 
  Lam1 f y {subst (Push (Push (Push r))) bod}      
 
-------------------------------------------------
-- Terms at level 0, indexed by terms at level 1
-- These are singleton types!

data Exp':: Exp e t ~> Env ~> Typ ~> *0 where
  Z0:: Exp' Z1 env NatT
  S0:: Exp' n env NatT -> Exp' (S1 n) env NatT
  If0:: Exp' tst env NatT -> 
        Exp' th env t -> 
        Exp' el env (ArrT NatT t) ->
        Exp' (If1 tst th el) env t
  App0:: forall (s::Typ) (t::Typ) (env::Env) 
                (f:: Exp env (ArrT s t)) (x:: Exp env s) .
         -- The explict signature is necessary to ensure that
         -- Exp' (f:: Exp env (Arr s t)) env (ArrT s t) 
         -- because s doesn't appear in the range of App0.
         Exp' f env (ArrT s t) ->
         Exp' x env s -> 
         Exp' (App1 f x) env t
  Var0:: Sym' x s -> Exp' (Var1 x) {s=t; env}e t
  Sh0:: Exp' x env t -> Exp' (Sh1 x) {s=q;env}e t
  Lam0  :: Sym' f g -> Sym' a y -> 
           Exp' bod {y=s,g=ArrT s t; env}e t ->
           Exp' (Lam1 f a bod) env (ArrT s t)
       
-----------------------------------------------------
-- Example

v x = Var0 x
v1 x = Sh0 (v x)
v2 x = Sh0 (v1 x)
v3 x = Sh0 (v2 x)
           
x = 0      

-- copy = \ copy x . if x then 0 else (\ n -> S(copy n))

copy = Lam0 C0 A0 
        (If0 (v A0) 
             Z0 
             (Lam0 D0 B0 (S0 (App0 (v3 C0) (v B0)))))

----------------------------------------------------------
-- Judgements for what it means to be a value
-- and what it means to take a step

data Value::  Exp env t ~> *0  where
 ValZ :: Value Z1
 ValS :: Value x -> Value (S1 x)
 ValLam:: Value (Lam1 f x body)
 
data Steps:: Exp e t ~> Exp e t ~> *0  where
 StepS :: Steps x y -> Steps (S1 x) (S1 y)
 StepApp1 :: Steps x y -> Steps (App1 x a) (App1 y a)
 StepApp2:: Value x -> Steps a b -> Steps (App1 x a) (App1 x b)
 
 StepApp3:: Value arg ->
            Steps (App1 (Lam1 f x body) arg)
                  {subst (Bnd x arg (Bnd f (Lam1 f x body) Id)) body}
                 
 StepIf:: Steps x y -> Steps (If1 x m n) (If1 y m n)
 StepIfZ:: Steps (If1 Z1 m n) m
 StepIfS:: Value x -> Steps (If1 (S1 x) m n) (App1 n x)

-------------------------------------------------------
-- The progress Lemma


progress:: forall (env :: Env)
                  (typ :: Typ)
                  (e  :: Exp Closed typ) . 
           Exp' e Closed typ -> 
           (Value e + exists (e' :: Exp Closed typ) .  Steps e e')
progress Z0 = L ValZ
progress (S0 x) = 
  case progress x of
    L p -> L(ValS p)
    R(Ex p) -> R(Ex(StepS p))
progress (term@(If0 tst th el)) = 
  case progress tst of
   L (ValZ) -> R (Ex StepIfZ)
   L (ValS p) -> R (Ex (StepIfS p))
   R (Ex p) -> R(Ex (StepIf p))
progress (term@(App0 f x)) =
  case progress f of
    L ValZ -> unreachable
    L (p1@ValLam) -> 
        case progress x of
           L p2 -> R(Ex (StepApp3 p2))
           R (Ex p2) -> R(Ex (StepApp2 p1 p2))
    R (Ex p1) -> R(Ex(StepApp1 p1))
progress (Lam0 f x bod) = L ValLam      
progress (Var0 _) = unreachable
progress (Sh0 _) = unreachable

