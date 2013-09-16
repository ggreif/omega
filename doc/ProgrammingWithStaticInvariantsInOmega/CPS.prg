












































































data Res = FinalAnswer







data Type t
       =          Int                    where t = Int
       | ex a b.  Arr (Type a) (Type b)  where t = a -> b
       |          Res                    where t = Res




































data Cmp e t   =           Val   (Val e t)
               |  ex s.    App   (Cmp e (s -> t)) (Cmp e s)

data Val e t   =           Lit   Int                     where t = Int
               |           Var   (Var e t) (Type t)
               |  ex a b.  Lam   (Type a) (Cmp (e,a) b)  where t = a -> b

data Var e t   =  ex f.    Zero                          where e = (f,t)
               |  ex f s.  Succ  (Var f t)               where e = (f,s)







zero  :: Type a -> Cmp (e,a) a
zero  t = Val (Var Zero t) 

one   :: Type a -> Cmp ((e,a),b) a
one   t = Val (Var (Succ Zero) t)

two   :: Type a -> Cmp (((e,a),b),c) a
two   t = Val (Var (Succ (Succ Zero)) t)
















expType  :: Cmp e t -> Type t
expType  (Val v)    = valType v
expType  (App m n)  = codomain (expType m)

valType  :: Val e t -> Type t
valType  (Lit i)    = Int
valType  (Var x t)  = t
valType  (Lam t n)  = Arr t (expType n)

codomain :: Type (a -> b) -> Type b
codomain (Arr a b)  = b











shift :: Cmp e t -> Cmp (e,s) t
shift e                   = shiftE Succ e

shiftE :: (forall t. Var e t -> Var f t) -> Cmp e t -> Cmp f t
shiftE    f  (App n m)    = App (shiftE f n) (shiftE f m)
shiftE    f  (Val v)      = Val (shiftV f v)

shiftV :: (forall t. Var e t -> Var f t) -> Val e t -> Val f t
shiftV    f  (Lit i)      = Lit i
shiftV    f  (Var x s)    = Var (f x) s
shiftV    f  (Lam s n)    = Lam s (shiftE (liftShift f) n)
 
liftShift :: (forall t. Var e t -> Var f t) -> Var (e,s) t -> Var (f,s) t
liftShift s  (Zero)       = Zero
liftShift s  (Succ x)     = Succ (s x)













cps   :: * ~> * ~> *
{cps   r t}          = ({cpsv r t} -> r) -> r

cpsv  :: * ~> * ~> *
{cpsv  r Int}        = Int
{cpsv  r (a -> b)}   = {cpsv r a} -> {cps r b}

cpse  :: * ~> * ~> *
{cpse  r ()}         = ()
{cpse  r (a,b)}      = ({cpse r a},{cpsv r b})




cpsT    :: Type r -> Type t -> Type {cps r t}
cpsT   r t          = Arr (Arr (cpsTv r t) r) r

cpsTv   :: Type r -> Type t -> Type {cpsv r t}
cpsTv  r Int        = Int
cpsTv  r (Arr a b)  = Arr (cpsTv r a) (cpsT r b)

























cpsX ::  Type r ->  Var  e a ->  Var  {cpse r e}  {cpsv  r a}
cpsX r (Zero)     = Zero
cpsX r (Succ x)   = Succ (cpsX r x)

cpsV ::  Type r ->  Val  e a ->  Val  {cpse r e}  {cpsv  r a}
cpsV r (Lit i)    = Lit i
cpsV r (Var x t)  = Var (cpsX r x) (cpsTv r t)
cpsV r (Lam t n)  = Lam (cpsTv r t) (cpsC r n)








cpsC :: Type r -> Cmp e a -> Cmp {cpse r e} {cps r a}
cpsC r (Val v)    = Val (Lam kt (App (zero kt) (shift (Val v'))))
    where  v'     = cpsV r v
           kt     = Arr (valType v') r

cpsC r (App m n)  = case expType m' of 
                    Arr (Arr (y0t@(Arr y1t (Arr kt _))) _) _ -> 
                       Val (Lam kt                                
                       (App (shift m')          (Val (Lam y0t     
                       (App (shift (shift n'))  (Val (Lam y1t     
                       (App (App (one y0t) (zero y1t)) (two kt))  
                       ))) ))) )
    where  m'     = cpsC r m
           n'     = cpsC r n



-- playing
exp = Val (Lam Int
     (Val (Lam (Arr Int Int)
     (App (zero (Arr Int Int)) (one Int)))))
 
test = cpsC Res exp
-- lam k. k (lam a. lam k. k (lam f. lam c. (lam k. k f) (lam d. (lam k. k a) (lam e. d e c))))



