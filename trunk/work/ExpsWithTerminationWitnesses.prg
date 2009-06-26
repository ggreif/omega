

----------------------------------------------
-- Natural Numbers

data Natural:: level n . *n where
   Zero :: Natural 
   Succ :: Natural ~> Natural  
 deriving Nat(n) 


-- Singleton Natural Numbers

data Natural' :: level n . Natural_(1) ~> *n where
  Zero' :: Natural' Zero
  Succ' :: Natural' n ~> Natural' (Succ n)
    deriving Nat(m)   

-------------------------------------------
-- Non-equality comparisons for Natural Numbers

data NatGT :: Natural ~> Natural ~> *0 where
  NatGTbase :: NatGT (Succ n) n
  NatGTstep :: NatGT n m -> NatGT (Succ n) m

data NatLT :: Natural ~> Natural ~> *0 where
  NatLTbase :: NatLT n (Succ n)
  NatLTstep :: NatLT n m -> NatLT n (Succ m)

data NatNEQ:: Natural ~> Natural ~> *0 where
  NeqGT :: NatGT n m -> NatNEQ n m
  NeqLT :: NatLT n m -> NatNEQ n m

-- Are two Naturals equal or not equal?

data NatTest:: Natural ~> Natural ~> *0 where
  NatDiff :: NatNEQ x y -> NatTest x y
  NatSame :: Equal x y -> NatTest x y
  
--------------------------------------------------------
-- Stages (depth or size of inductively defined data)

data Stage:: Natural ~> *1 where
  V:: Natural ~> Stage t
  N:: Stage t ~> Stage t
  Inf:: Stage t
  
data Stage':: Stage n ~> *0 where
  V:: Natural' n -> Stage' (V n)
  N :: Stage' s -> Stage' (N s)
  Inf :: Stage' Inf

----------------------------------------------------
-- Types and Indexes to types 
-- (Types are singeltons) and Environments

data TypeIndex:: *1 where
  VarT :: Natural ~> TypeIndex
  NatT :: Stage n ~> TypeIndex
  ListT :: Stage n ~> TypeIndex ~> TypeIndex
  ArrT :: TypeIndex ~> TypeIndex ~> TypeIndex


data Typ :: TypeIndex ~> *0 where
  VarT :: Natural' n -> Typ (VarT n)
  NatT :: Stage' s -> Typ (NatT s) 
  List :: Stage' s -> Typ t -> Typ (ListT s t)
  ArrT :: Typ t -> Typ u -> Typ (ArrT t u)

data Env:: *2 where
  Closed :: Env
  ConsEnv :: Natural ~> TypeIndex ~> Env ~> Env
 deriving Record(e)

------------------------------------------------
-- Semantic Equality Witness for Stages

data StageEQ :: Stage s ~> Stage s ~> *0 where
  StEq :: StageEQ s s
  StStep :: StageEQ s1 s2 -> StageEQ (N s1) (N s2)
  StTrans :: StageEQ s1 s2 -> StageEQ s2 s3 -> StageEQ s1 s3
  StSymm :: StageEQ s1 s2 -> StageEQ s2 s1
  StInf :: StageEQ s Inf -> StageEQ (N s) Inf

------------------------------------------------
-- Less Than or Equal Witness for Stages

data LeqSt:: Stage a ~> Stage b ~> *0 where
  Same :: LeqSt x x 
  Reach :: LeqSt x y -> LeqSt x (N y)
  All :: LeqSt x Inf
  Both :: LeqSt x y -> LeqSt (N x) (N y)

-- Equal witness for TypeIndex

data LeqTy :: TypeIndex ~> TypeIndex ~> *0 where
  EqTy :: LeqTy t t
  LeqTy0 :: LeqSt i j -> LeqTy (NatT i) (NatT j)
  LeqTy1s :: LeqSt i j -> LeqTy (ListT i x) (ListT j x)
  LeqTy1t :: LeqTy a b -> LeqTy (ListT i a) (ListT i b)
  LeqTyArr :: LeqTy t' t -> LeqTy u u' -> LeqTy (ArrT t u) (ArrT t' u')
  
------------------------------------------------
-- Does a Stage Variable Occurr in a TypeIndex?

data AppearsPos :: Natural ~> TypeIndex ~> *0 where
  SPVar :: AppearsPos i (VarT x)
  SPArr :: AppearsNeg i t -> AppearsPos i u -> AppearsPos i (ArrT t u)
  SPNat :: AppearsPos i (NatT s)
  SPList :: AppearsPos i t -> AppearsPos i (ListT s t)
  
data AppearsNeg :: Natural ~> TypeIndex ~> *0 where
  SN1 :: AppearsNeg i (VarT x)
  SN2 :: AppearsPos i t -> AppearsNeg i u -> AppearsNeg i (ArrT t u)
  SNNat :: NoOcc i s -> AppearsNeg i (NatT s)
  SNList :: NoOcc i s -> AppearsNeg i t -> AppearsNeg i (ListT s t)

-- no occurrences of stage variable names in a type

data NoOcc :: Natural ~> Stage y ~> *0 where
  NoOccV :: NatNEQ i j -> NoOcc i (V j)
  NoOccN :: NoOcc i s -> NoOcc i (N s)
  NoOccInf :: NoOcc i Inf
  
--------------------------------------------------
-- Relations that stages and type indexes are related 
-- by substitution of stage variables

data SubsSt:: Natural ~> Stage a ~> Stage b ~> Stage c ~> *0 where
  Sub0 :: NoOcc x a -> StageEQ a b -> SubsSt x y a b
  SubV :: SubsSt x y (V x) y
  SubN :: SubsSt x y a b -> SubsSt x y (N a) (N b)
  
data SubsTy :: Natural ~> Stage a ~> TypeIndex ~> TypeIndex ~> *0 where
  SubVar :: SubsTy n s (VarT x) (VarT x)
  SubTC0 :: SubsSt n s s1 s2 -> SubsTy n s (NatT s1) (NatT s2)
  SubTC1 :: SubsSt n s s1 s2
         -> SubsTy n s t1 t2 -> SubsTy n s (ListT s1 t1) (ListT s2 t2)
  SubArr :: SubsTy n s t1 t2 -> SubsTy n s u1 u2
         -> SubsTy n s (ArrT t1 u1) (ArrT t2 u2)
  
------------------------------------------------------------
-- Abstract syntax for patterns, case arms, and terms

data Pat:: Env ~> Env ~> TypeIndex ~> *0 where -- Inf problem? don't have coerce
  Wp :: Pat e e t
  Vp :: Natural' n -> Pat e (ConsEnv n t e) t
  Zp :: Pat e e (NatT (N x))
  Sp :: Pat e f (NatT x) -> Pat e f (NatT (N x))
  NilP :: Pat e e (ListT (N x) a)
  ConsP :: Pat e f a -> Pat f g (ListT x a) -> Pat e g (ListT (N x) a)
  
data Arms:: Env ~> TypeIndex ~> TypeIndex ~> *0  where
  NilArm :: Arms e x y
  ConsArm:: Pat e1 e2 x -> Exp e2 y -> Arms e1 x y -> Arms e1 x y
 deriving Record(a)


data Exp:: Env ~> TypeIndex ~> *0 where
  Ze :: Exp env (NatT (N s))
  Se :: Exp env (NatT s) -> Exp env (NatT (N s))
  NilE :: Exp env (ListT (N s) a)
  ConsE :: Exp env a -> Exp env (ListT s a) -> Exp env (ListT (N s) a)

  App :: Exp env (ArrT s t) -> Exp env s -> Exp env t

  Var :: Natural' s -> Exp {s=t; env}e t
  Sh :: Exp env t -> Exp {s=q;env}e t
  Fn :: Arms e s t -> Exp e (ArrT s t)
 
  Fix0 :: Exp {f=ArrT (tc (V i)) a; env}e (ArrT (tc (N (V i))) b)
       -> SubsTy i (N (V i)) a b -> SubsTy i s a c -> AppearsPos i a
       -> Exp env (ArrT (tc s) c)

  Fix1 :: Exp {f=ArrT (tc (V i) t) a; env}e (ArrT (tc (N (V i)) t) b)
       -> SubsTy i (N (V i)) a b -> SubsTy i s a c -> AppearsPos i a
       -> Exp env (ArrT (tc s t) c)

--  HasTy :: Exp env a -> Ty' b -> LeqTy a b -> Exp env b

  Coerce:: LeqTy a b -> Exp env a -> Exp env b
  

------------------------------------------------
-- Examples


v0 x = Var x
v1 x = Sh (v0 x)
v2 x = Sh (v1 x)
v3 x = Sh (v2 x)
v4 x = Sh (v3 x)

-- shorthands

ap = App

caseE e alts = Fn alts `ap` e

lamE x e = Fn {Vp x=e}a

eqInf0 :: SubsSt a b Inf Inf  
eqInf0 = Sub0 NoOccInf StEq -- e.g., (Nat Inf) is equal to (Nat Inf)


-----------------------------------------------
-- Small Programs


-- copy = Fix (\ copy -> (\ Z -> Z | (S m) -> S (copy m)))
copy = Fix0 body2 (SubTC0 SubV) (SubTC0 SubV) SPNat
  where body2 = Fn { Zp         = Ze
                   , Sp (Vp 0m) = Se (v1 2m `ap` v0 0m)
                   }a
        copy = 0m
        n = 1m
        m = 2m
  