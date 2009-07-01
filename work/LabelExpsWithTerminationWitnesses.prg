

--------------------------------------------------------
-- Stages (depth or size of inductively defined data)

data Stage:: Tag ~> *1 where
  V:: Tag ~> Stage t
  N:: Stage t ~> Stage t
  Inf:: Stage t
  
data Stage':: Stage n ~> *0 where
  V:: Label n -> Stage' (V n)
  N :: Stage' s -> Stage' (N s)
  Inf :: Stage' Inf


----------------------------------------------------
-- Types and Type Indexes 
-- (Types are singletons) and Environments

data TypeIndex:: *1 where
  VarT :: Tag ~> TypeIndex
  NatT :: Stage n ~> TypeIndex
  ListT :: Stage n ~> TypeIndex ~> TypeIndex
  ArrT :: TypeIndex ~> TypeIndex ~> TypeIndex
  
-- ArrT :: TypeIndex ~> Totality ~> TypeIndex ~> TypeIndex

data Typ :: TypeIndex ~> *0 where
  VarT :: Label n -> Typ (VarT n)
  NatT :: Stage' s -> Typ (NatT s) 
  List :: Stage' s -> Typ t -> Typ (ListT s t)
  ArrT :: Typ t -> Typ u -> Typ (ArrT t u)

data Env:: *2 where
  Closed :: Env
  ConsEnv :: Tag ~> TypeIndex ~> Env ~> Env
 deriving Record(e)

------------------------------------------------
-- Semantic Equality Witness for Stages

data StageEQ :: Stage s ~> Stage s ~> *0 where
  StEq :: StageEQ s s
  StStep :: StageEQ s1 s2 -> StageEQ (N s1) (N s2)
  StTrans :: StageEQ s1 s2 -> StageEQ s2 s3 -> StageEQ s1 s3
  StSymm :: StageEQ s1 s2 -> StageEQ s2 s1
  StInf :: StageEQ s Inf -> StageEQ (N s) Inf 
           -- Here is where semantic equality differs from syntactic equality

------------------------------------------------
-- Less Than or Equal Witness for Stages

data LeqSt:: Stage a ~> Stage b ~> *0 where
  Same :: LeqSt x x 
  Reach :: LeqSt x y -> LeqSt x (N y)
  All :: LeqSt x Inf
  Both :: LeqSt x y -> LeqSt (N x) (N y)

-- Equal Witness for TypeIndex

data LeqTy :: TypeIndex ~> TypeIndex ~> *0 where
  EqTy :: LeqTy t t
  LeqTy0 :: LeqSt i j -> LeqTy (NatT i) (NatT j)
  LeqTy1s :: LeqSt i j -> LeqTy (ListT i x) (ListT j x)
  LeqTy1t :: LeqTy a b -> LeqTy (ListT i a) (ListT i b)
  LeqTyArr :: LeqTy t' t -> LeqTy u u' -> LeqTy (ArrT t u) (ArrT t' u')


------------------------------------------------
-- Does a Stage Variable Occur in a TypeIndex?

data AppearsPos :: Tag ~> TypeIndex ~> *0 where
  SPVar :: AppearsPos i (VarT x)
  SPArr :: AppearsNeg i t -> AppearsPos i u -> AppearsPos i (ArrT t u)
  SPNat :: AppearsPos i (NatT s)
  SPList :: AppearsPos i t -> AppearsPos i (ListT s t)
  
data AppearsNeg :: Tag ~> TypeIndex ~> *0 where
  SN1 :: AppearsNeg i (VarT x)
  SN2 :: AppearsPos i t -> AppearsNeg i u -> AppearsNeg i (ArrT t u)
  SNNat :: NoOcc i s -> AppearsNeg i (NatT s)
  SNList :: NoOcc i s -> AppearsNeg i t -> AppearsNeg i (ListT s t)

-- no occurrences of stage variable names in a type

data NoOcc :: Tag ~> Stage y ~> *0 where
  NoOccV :: DiffLabel i j -> NoOcc i (V j)
  NoOccN :: NoOcc i s -> NoOcc i (N s)
  NoOccInf :: NoOcc i Inf
  
 
--------------------------------------------------
-- Relations that stages and type indexes are related 
-- by substitution of stage variables

data SubsSt:: Tag ~> Stage a ~> Stage b ~> Stage c ~> *0 where
  Sub0 :: NoOcc x a -> StageEQ a b -> SubsSt x y a b
  SubV :: SubsSt x y (V x) y
  SubN :: SubsSt x y a b -> SubsSt x y (N a) (N b)
  
data SubsTy :: Tag ~> Stage a ~> TypeIndex ~> TypeIndex ~> *0 where
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
  Vp :: Label n -> Pat e (ConsEnv n t e) t
  Zp :: Pat e e (NatT (N x))
  Sp :: Pat e f (NatT x) -> Pat e f (NatT (N x))
  NilP :: Pat e e (ListT (N x) a)
  ConsP :: Pat e f a -> Pat f g (ListT x a) -> Pat e g (ListT (N x) a)
  CastP :: Pat e1 e2 a -> LeqTy b a -> Pat e1 e2 b
           -- OK for patterns to match smaller things when needed


  
data Arms:: Env ~> TypeIndex ~> TypeIndex ~> *0  where
  NilArm :: Arms e x y
  ConsArm:: Pat e1 e2 x -> Exp e2 y -> Arms e1 x y -> Arms e1 x y
 deriving Record(a)

-- data Exp:: Env ~> TypeIndex ~> *0 where
--  Ze :: Exp env (NatT (N s)) 
--  Se :: Exp env (NatT s) -> Exp env (NatT (N s)) 
--  Lam :: Exp {f=a;env} b -> Exp env (Arr a 1 b)
--  App :: Exp env (ArrT s j t) -> Exp env s -> Exp env t 
--  Fix0 :: Exp {f=ArrT (tc (V i)) w2 a; env}e (ArrT (tc (N (V i))) (N w2) a) ->
--          Exp env (ArrT (tc s) (N (V i)) a) 
       
       
data Exp:: Env ~> TypeIndex ~> *0 where
  Ze :: Exp env (NatT (N s))
  Se :: Exp env (NatT s) -> Exp env (NatT (N s))
  NilE :: Exp env (ListT (N s) a)
  ConsE :: Exp env a -> Exp env (ListT s a) -> Exp env (ListT (N s) a)

  App :: Exp env (ArrT s t) -> Exp env s -> Exp env t

  Var :: Label s -> Exp {s=t; env}e t
  Sh :: Exp env t -> Exp {s=q;env}e t
  Fn :: Arms e s t -> Exp e (ArrT s t)
 
  Fix0 :: Exp {f=ArrT (tc (V i)) a; env}e (ArrT (tc (N (V i))) b)
       -> SubsTy i (N (V i)) a b -> SubsTy i s a c -> AppearsPos i a
       -> Exp env (ArrT (tc s) c)

  Fix1 :: Exp {f=ArrT (tc (V i) t) a; env}e (ArrT (tc (N (V i)) t) b)
       -> SubsTy i (N (V i)) a b -> SubsTy i s a c -> AppearsPos i a
       -> Exp env (ArrT (tc s t) c)
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


-- copy = Fix copy (\ Z -> Z | (S m) -> S (copy m))
copy = Fix0 (Fn { Zp = Ze
                , Sp (Vp `m) = Se (v1 `copy `ap` v0 `m) }a) 
            p1 p1 p3
  where p1 = (SubTC0 SubV) 
        p3 = SPNat
  

---------------------------------------------        
-- mymap = \ f -> Fix map (\ Nil -> Nil
--                         | Cons x xs -> Cons (f x) (map xs))
mymap = lamE `f $
          Fix1 (Fn { NilP = NilE
                   , ConsP (Vp `x) (Vp `xs) = ConsE (v3 `f `ap` v1 `x) 
                                                    (v2 `map `ap` v0 `xs)
                   }a) p1 p2 p3
  where p1 = (SubTC1 SubV SubVar) 
        p2 = (SubTC1 SubV SubVar) 
        p3 = (SPList SPVar)

------------------------------------
-- half = Fix half (\ Z -> Z
--                  | (S Z) -> Z
--                  | (S (S n)) -> half n))

body4a = Fn{ Zp              = Ze
          , Sp Zp           = Ze
          , Sp (Sp (Vp `n)) = Se(ap (v1 `half) (v0 `n))
          }a
          
body4b = Coerce (LeqTyArr (LeqTy0 (Reach Same)) EqTy) body4a

body4c= Fn{ Zp         = Ze
          , Sp (Vp `m) = caseE (Coerce (LeqTy0 (Reach Same)) (v0 `m))
                             { Zp          = Ze
                             , Sp (Vp `n) = Se (v2 `half `ap` v0 `n)
                             }a
          }a  

body4d = Fn{ Zp                         = Ze
           , CastP (Sp Zp) p1           = Ze
           , CastP (Sp (Sp (Vp `n))) p1 = Se(ap (v1 `half) (v0 `n))
           }a
  where p1 = LeqTy0 (Reach Same)
  

showSameType = [body4b, body4c, body4d]
          
half = Fix0 body4c p1 p2 p3
  where p1 = (SubTC0 SubV) 
        p2 = (SubTC0 SubV) 
        p3 = SPNat          
        
-------------------------------------------
-- double = Fix double (\ Z -> Z
--                      | (S n) -> S (S (double n)))


body5 = Fn { Zp         = Ze
           , Sp (Vp `x) = Se (Se (v1 `double `ap` v0 `x))
           }a
           
       

double = Fix0 (Coerce (EqTy `LeqTyArr` LeqTy0 All) body5) p1 p2 p3
   where p1 = (SubTC0 eqInf0) 
         p2 = (SubTC0 eqInf0) 
         p3 = SPNat


--------------------------------------------
-- plus = Fix plus (\ Z -> (\ y -> y)
--                  | (S x) -> \ y -> S(plus x y))


body6 = Fn { Zp         = lamE `y (v0 `y)
           , Sp (Vp `x) = lamE `y (Coerce (LeqTy0 All)
                                          (Se (v2 `plus `ap` v1 `x `ap` v0 `y)))
           }a
           

plus = Fix0 body6 p1 p2 p3
  where p1 = (SubArr (SubTC0 eqInf0) (SubTC0 eqInf0))
        p2 = (SubArr (SubTC0 eqInf0) (SubTC0 eqInf0))
        p3 = (SPArr (SNNat NoOccInf) SPNat)
        
------------------------------------------------
-- plus' = Fix plus (\ x y -> case x of
--                              Z -> y
--                              (S z) -> S(plus z y))

body6' = lamE `x $ lamE `y $
  caseE (v1 `x)
      { Zp         = Coerce (LeqTy0 All) $ v0 `y
      , Sp (Vp `z) = Coerce (LeqTy0 All) $ Se (v3 `plus' `ap` v0 `z `ap` v1 `y)
      }a

plus' = Fix0 body6' p1 p2 p3
  where p1 = (SubArr (SubTC0 eqInf0) (SubTC0 eqInf0))
        p2 = (SubArr (SubTC0 eqInf0) (SubTC0 eqInf0))
        p3 = (SPArr (SNNat NoOccInf) SPNat)


-----------------------------------------------------
-- append = Fix append (\ Nil -> (\ ys -> ys)
--                      | (Cons x xs) -> (\ ys -> Cons x (append xs ys)))

body7 = Fn { NilP = lamE `ys (v0 `ys)
           , ConsP (Vp `x) (Vp `xs)
                  = lamE `ys (Coerce (LeqTy1s All) 
                                     (ConsE (v2 `x) (v3 `append `ap` v1 `xs `ap` v0 `ys)))
           }a

append = Fix1 body7 p1 p2 p3
  where p1 = (SubArr (SubTC1 eqInf0 SubVar) (SubTC1 eqInf0 SubVar))
        p2 = (SubArr (SubTC1 eqInf0 SubVar) (SubTC1 eqInf0 SubVar))
        p3 = (SPArr (SNList NoOccInf SN1) (SPList SPVar))
        

----------------------------------------------------
-- length = Fix length (\ Nil -> Z
--                      | (Cons x xs) -> S(length xs)

body9 = Fn { NilP                  = Ze
           , ConsP (Vp `x) (Vp `xs) = Se (v2 `length `ap` v0 `xs)
           }a

length = Fix1 body9 p1 p2 p3
  where p1 = (SubTC0 SubV) 
        p2 = (SubTC0 SubV) 
        p3 = SPNat


----------------------------------------
-- minus = Fix minus 
--             (\ x y -> case x of
--                         Z -> x
--                        (S n) -> case y of
--                                   Z -> x 
--                                   (S m) -> minus n m)


body10 = lamE `x $ lamE `y $
  caseE (v1 `x)
      { Zp         = v1 `x
      , Sp (Vp `n) = caseE (v1 `y)
                          { Zp         = v2 `x
                          , Sp (Vp `m) = Coerce (LeqTy0 (Reach Same))
                                                (v4 `minus `ap` v1 `n `ap` v0 `m)
                          }a
      }a

minus = Fix0 body10
      (SubArr (SubTC0 (Sub0 NoOccInf (StSymm $ StInf StEq))) (SubTC0 SubV))
      (SubArr (SubTC0 (Sub0 NoOccInf (StSymm $ StInf StEq))) (SubTC0 SubV))
      (SNNat NoOccInf `SPArr` SPNat)


minusCoerced = Coerce (EqTy `LeqTyArr` ( (LeqTy0 (Reach Same)) `LeqTyArr` EqTy)) minus

-- Alternate minus

body10' = 
  Coerce (EqTy `LeqTyArr` ((LeqTy0 (Reach Same)) `LeqTyArr` EqTy)) 
         (Fn { Zp         = Fn { Vp `m      = Ze }a
             , Sp (Vp `n) = Fn { Zp         = Se (v0 `n)
                               , Sp (Vp `m) = Coerce (LeqTy0 (Reach Same)) 
                                                     (v2 `minus `ap` v1 `n `ap` v0 `m)
                               }a
             }a)
             
minus' = Fix0 body10' p1 p2 p3
  where p1 = (SubArr (SubTC0 eqInf0) (SubTC0 SubV))
        p2 = (SubArr (SubTC0 eqInf0) (SubTC0 SubV))
        p3 = (SNNat NoOccInf `SPArr` SPNat)
        
---------------------------------------------
-- divide = Fix divide (\ Z -> (\ m -> Z)
--                      | (S n) -> (\ m -> S(divide (minus n m)  m)))

body11 =
  Fn { Zp         = lamE `m Ze
     , Sp (Vp `n) = lamE `m $
                      Se (v2 `dv `ap` (minus' `ap` v1 `n `ap` v0 `m) `ap` v0 `m)
     }a

divide = Fix0 body11 p1 p2 p3
  where p1 = (SubArr (SubTC0 eqInf0) (SubTC0 SubV))
        p2 = (SubArr (SubTC0 eqInf0) (SubTC0 SubV))
        p3 = (SPArr (SNNat NoOccInf) SPNat)

-----------------------------------------------------
-- ack = 
--   Fix ack 
--       (\ Z -> (\ m -> m)
--        | (S n) -> Fix ack_x (\ Z -> ack n (S Z)
--                              | (S m) -> ack n (ack_x m)))

body12 = Fn { Zp         = lamE `m (v0 `m)
            , Sp (Vp `n) = Fix0 body13 (SubTC0 eqInf0) (SubTC0 eqInf0) SPNat
            }a

-- body13 in the context of second arm of body12
-- we use names 3m for ack and 4m for ack_x
 
body13 =
  Fn { Zp         = v2 `ack `ap` v1 `n `ap` Coerce (LeqTy0 All) (Se Ze)
     , Sp (Vp `m) = v3 `ack `ap` v2 `n `ap` Coerce (LeqTy0 All) (v1 `ack_x `ap` v0 `m)
     }a

ack = Fix0 body12 p1 p2 p3
  where p1 = (SubArr (SubTC0 eqInf0) (SubTC0 eqInf0))
        p2 = (SubArr (SubTC0 eqInf0) (SubTC0 eqInf0))
        p3 = (SPArr (SNNat NoOccInf) SPNat)

-------------------------------------------------------------
-- weird1 = Fix weird1 (\ Z -> Z
--                      | (S n) -> S(weird1 (copy n)))
-- works because copy is size preserving!!

body14 = Fn { Zp = Ze
            , Sp (Vp `n) = Se (v1 `weird1 `ap` (copy `ap` v0 `n)) }a
            
body14b = Fn { Zp = Ze -- This is the constant zero function
            , Sp (Vp `n) = Coerce (LeqTy0 (Reach Same)) 
                                  (v1 `weird1 `ap` (copy `ap` v0 `n)) }a 
                                 

sameType14 = [body14, body14b]
            
weird1 = Fix0 body14 (SubTC0 SubV) (SubTC0 SubV) SPNat