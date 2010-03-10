
data Cd n f t = Cd (forall p . Exp p n f t)

-----------------------------------------

data Var :: *0 ~> *0 ~> *0 where
   Zv :: Var ((t,a)) t
   Sv :: (Var g1 t) -> Var ((t1,g1)) t

data Exp :: *0 ~> *0 ~> *0 ~> *0 ~> *0 where
   Const :: t -> Exp past now future t
   V :: (Var now t) -> Exp past now future t
   Abs :: (Exp past ((t1,now)) future t2) -> Exp past now future (t1 -> t2)
   App :: (Exp past now future (t1 -> t)) -> (Exp past now future t1) -> Exp past now future t
   Br :: (Exp ((past,now)) n f w) -> Exp past now ((n,f)) (Cd n f w)
   Br2 :: (Exp ((past,now)) n f w) -> Exp past now ((n,f)) (Exp z n f w)
   Esc :: (Exp p n ((now,future)) (Cd now future t)) -> Exp ((p,n)) now future t
   Esc2 :: ((forall z . Exp p n ((now,future)) (Exp z now future t))) -> Exp ((p,n)) now future t
   Csp :: (Exp p n ((now,future)) t) -> Exp ((p,n)) now future t
   Pair :: (Exp past now future a) -> (Exp past now future b) -> Exp past now future ((a,b))
   Run :: ((forall n . Exp past now ((n,future)) (Cd n future t))) -> Exp past now future t
   
   Run2 :: ((forall n z . Exp past now ((n,future)) (Exp z n future t))) -> Exp past now future t
   Lam1 :: Exp past now future ((Exp d ((e,a)) b c) -> Exp d a b (e -> c))
   App1 :: Exp past now future ((Exp d e a (b -> c)) -> (Exp d e a b) -> Exp d e a c)
   Const1 :: Exp past now future (d -> Exp e a b d)
   Var1 :: Exp past now future ((Var d e) -> Exp a d b e)
   Pair1 :: Exp past now future ((Exp d e a b) -> (Exp d e a c) -> Exp d e a ((b,c)))


data Env :: *0 ~> *0 ~> *0 where
   EnvZ :: b -> Env ((a,b)) y
   EnvS :: (Env x' y') -> Env ((x',c)) ((y',c))

v1 = Const V
lam1 = Const Abs
app1 = Const App
const1 = Const Const
pair1 = Const Pair
unCd1 = Const unCd where unCd (Cd x) = x

trans :: Exp p n f t -> Exp x n y t
trans (V v) = V v
trans (App f x)= App (trans f) (trans x)
trans (Abs e) = Abs(trans e)
trans (Pair x y) = Pair (trans x) (trans y)
trans (Const t) = Const t
trans (Br2 e) = tran1 e
trans (Run2 e) = App (Const (eval ())) (trans e)

tran1 :: Exp (a,b) n f t -> Exp p1 b f1 (Exp p2 n f t)
tran1 (V v) = App Var1 (Const v)
tran1 (Abs e) = App Lam1 (tran1 e)
tran1 (App f x) = App (App App1 (tran1 f)) (tran1 x)
tran1 (Const n) = App Const1 (Const n)
tran1 (Pair x y) = App (App Pair1 (tran1 x)) (tran1 y)
tran1 (Run2 e) = (App (Const (eval undefined)) (tran1 e))
tran1 (Esc2 e) = (trans e)
tran1 (Br2 e) = tran1(tran1 e)  -- tran2 e

tran2 :: Exp ((a,b),c) n f t -> 
         Exp p1 b f1 (Exp p2 c (n,f) (Exp p3 n f t))
tran2 x = undefined
tran2 (Esc2 e) = tran1 e
tran2 (Br2 e) = tran3 e

tran3 :: Exp (((a,b),c),d) n f t -> 
         Exp b1 b f1 (Exp p c (d,(n,f)) (Exp q d (n,f) (Exp r n f t)))
tran3 x = undefined         
tran3 (Esc2 e) = tran2 e


f x = x + 3
x1 = (Br2 (App (Const f) (Const 1))) 

fst (x,y) = x
snd (x,y) = y

eval0 :: (forall p . Exp p n f t) -> n -> t
eval0 e env = eval env e 

eval :: now -> Exp past now future t -> t
eval env (Const n) = n
-- eval (x,y) (V Zv) = x  -- This is a left-Right fact problem
-- eval (x,y) (V (Sv v)) = eval y (V v)
eval env (V Zv) = fst env
eval env (V (Sv v)) = eval (snd env) (V v)
eval env (App f x) = (eval env f) (eval env x)
eval env (Abs e) = \ v -> eval (v,env) e 
eval env (Pair x y) = (eval env x, eval env y)
eval env (Br e) = Cd (bd (EnvZ env) e)
eval env (Br2 e) = bd (EnvZ env) e
eval env (Run e) = case eval env e of { Cd x -> eval () x }
eval env (Run2 e) = eval () (eval env e)
eval env Lam1 = Abs
eval env App1 = App
eval env Const1 = Const
eval env Pair1 = Pair
eval env Var1 = V
eval env e = error "not defined"

  
bd :: Env a z -> Exp a n f t -> Exp z n f t
bd (EnvZ env) (Esc e) = case eval env e of { Cd x -> x}
bd (EnvS r) (Esc e) = case bd r e of { Br x -> x; y -> Esc y }
bd (EnvZ env) (Esc2 e) = eval env e
bd (EnvS r) (Esc2 e) = Esc2(bd r e)

bd (EnvZ env) (Csp e) = Const(eval env e)
bd (EnvS r) (Csp e) = Csp(bd r e)
bd env (Br e) = Br(bd (EnvS env) e)
bd env (Const n) = Const n 
bd env (V z) = V z
bd env (Abs e) = Abs(bd env e)
bd env (App x y) = App (bd env x) (bd env y)
bd env (Pair x y) = Pair (bd env x) (bd env y)
bd env (Run e) = Run(bd env e)


shv :: Var e t -> Int
shv Zv = 0
shv (Sv x) = 1 + shv x

she :: Exp p n f t -> String
she (V v) = "x"++ show (shv v)
she (Abs x) = "(\\->"++she x++")"
she (App x (y@(App _ _))) = she x++"("++she y++")"
she (App x y) = she x++" "++she y
she (Br2 e) = "<"++she e++">"
she (Esc2 (V v)) = "~x"++show (shv v)
she (Esc2 x) = "~("++she x++")"
she (Const x) = "%"++show x
she (Pair x y) = "("++she x++","++she y++")"
she (Run2 x) = "(run "++she x++")"
she Lam1 = "Lam1"
she App1 = "App1"
she Const1 = "Const1"
she Var1 = "Var1"
she Pair1 = "Pair1"

-----------------------------------------------------------------
compose f g x = f (g x)

-----------------------------------------------------------------
{-

Cd :: (forall 'b . Exp 'b c d e) -> Cd c d e

EnvZ :: b -> Env (c,b) d
EnvS :: Env e f -> Env (e,g) (f,g)

V    :: Var b c                                 -> Exp d b e c
Abs  :: Exp f (g,h) i j                         -> Exp f h i (g -> j)
App  :: Exp k l m (n -> o)                      -> Exp k l m n -> Exp k l m o
Br   :: Exp (p,q) r s t                         -> Exp p q (r,s) (C r s t)
Esc  :: Exp u v (w,x) (C w x y)                 -> Exp (u,v) w x y
Csp  :: Exp b c (d,e) f                         -> Exp (b,c) d e f
Pair :: Exp g h i j -> Exp g h i k              -> Exp g h i (j,k)
Run  :: (forall 'l . Exp m n ('l,o) (C 'l o p)) -> Exp m n o p

b1 :: (a,b) -> Exp (a,b) n f t -> Exp z n f t
b1 (a,b) (EnvS e) = case eval a b e of { C x -> x}
b1 (a,b) (Br e) = Br(b2 ((a,b),undefined) e)

b2 :: ((a,b),c) -> Exp ((a,b),c) n f t -> Exp (z,c) n f t
b2 ((a,b),c) (EnvS e) = EnvS(b1 (a,b) e)
b2 ((a,b),c) (Br e) = Br(b3 (((a,b),c),undefined) e)

b3 :: (((a,b),c),d) -> Exp (((a,b),c),d) n f t -> Exp ((z,c),d) n f t
b3 (((a,b),c),d) (EnvS e) = EnvS(b2 ((a,b),c) e)
b3 (((a,b),c),d) (Br e) = Br(b4 ((((a,b),c),d),undefined) e)
b3 env (Const n) = Const n 
b3 env (V z) = V z
b3 env (Abs e) = Abs(b3 env e)
b3 env (App x y) = App (b3 env x) (b3 env y)
b3 env (Pair x y) = Pair (b3 env x) (b3 env y)

b4 :: ((((a,b),c),d),e) -> Exp ((((a,b),c),d),e) n f t -> Exp (((z,c),d),e) n f t
b4 ((((a,b),c),d),e) (EnvS e) = EnvS(b3 (((a,b),c),d) e)


-}

-------------------------------------------------------

data FOAS :: *0 ~> *0 ~> *0 where
   FLift :: t -> FOAS env t
   FOne :: FOAS ((t,g)) t
   FShift :: (FOAS g t) -> FOAS ((a,g)) t
   FLam :: (FOAS ((a1,env)) a2) -> FOAS env (a1 -> a2)
   FApp :: (FOAS env (a -> t)) -> (FOAS env a) -> FOAS env t
   FPair :: (FOAS env a) -> (FOAS env b) -> FOAS env ((a,b))
   FRun :: ((forall g . FOAS env (FOAS g t))) -> FOAS env t
   FFix :: (FOAS ((t,env)) t) -> FOAS env t
   FCd :: ((forall p . FOAS env (Exp p n f w))) -> FOAS env (Cd n f w)
   FunCd :: (FOAS env (Cd n f w)) -> FOAS env (Exp p n f w)
   CLift :: (FOAS env s) -> FOAS env (Cd g f s)
   COne :: FOAS env (Cd ((s,g)) f s)
   CShift :: (FOAS env (Cd g f s)) -> FOAS env (Cd ((a,g)) f s)
   CLam :: (FOAS env (Cd ((a1,g)) f a2)) -> FOAS env (Cd g f (a1 -> a2))
   CApp :: (FOAS env (Cd n f (a -> s))) -> (FOAS env (Cd n f a)) -> FOAS env (Cd n f s)
   CPair :: (FOAS env (Cd n f a)) -> (FOAS env (Cd n f b)) -> FOAS env (Cd n f ((a,b)))


{-
v1 = FLift V
lam1 = FLift Abs
app1 = FLift App
const1 = FLift Const
pair1 = FLift Pair
unCd1 = FLift unCd where unCd (Cd x) = x


trans :: Exp p n f t -> FOAS n t
trans (V Zv) = FOne
trans (V (Sv n)) = FShift(trans (V n))
trans (App f x)= FApp (trans f) (trans x)
trans (Abs e) = FLam(trans e)
trans (Pair x y) = FPair (trans x) (trans y)
trans (Const t) = FLift t
trans (Br e) = FCd (tran1 e)
trans (Br e) = tra1 e

tran1 :: Exp (a,b) n f t -> FOAS b (Exp z n f t)
tran1 (V v) = FApp v1 (FLift v)
tran1 (Abs e) = FApp lam1 (tran1 e)
tran1 (App f x) = FApp (FApp app1 (tran1 f)) (tran1 x)
tran1 (Const n) = FApp const1 (FLift n)
tran1 (Pair x y) = FApp (FApp pair1 (tran1 x)) (tran1 y)
tran1 (Esc e) = FApp unCd1 (trans e)
tran1 (Br e) = tran2 e


tran2 :: Exp ((a,b),c) n f t -> FOAS b (Exp i c (n,f) (Cd n f t))
tran2 x = undefined
--tran2 (App x y) = check undefined -- FApp (FApp (FLift app1) (tran2 x)) (tran2 y)


tra1 :: Exp (a,b) n f t -> FOAS b (Cd n f t)
tra1 (V v) = FCd(FApp v1 (FLift v))
tra1 (Abs e) = case tra1 e of
                FCd x -> (FCd(FApp lam1 x))
                y -> FCd(FApp lam1 (FunCd y))
tra1 (Esc e) = trans e
tra1 (Br e) = tra2 e

tra2 :: Exp ((h,a),b) e f g ->  FOAS a (Cd b (e,f) (Cd e f g))
tra2 x = undefined

--traN app2 (App f x) = check (FApp (FApp app2 (FunCd(FunCd(tra2 f)))) (FunCd(FunCd(tra2 x))))
-}


{--

trans1 :: Exp (a,b) n f t -> FOAS b (Cd n f t)
trans1 (Const n) = CLift(FLift n)
trans1 (App f x) = CApp (trans1 f) (trans1 x)
trans1 (Abs e) = CLam (trans1 e)
trans1 (V Z) = COne
trans1 (V (S v)) = CShift(trans1 (V v))
trans1 (Pair x y) = CPair (trans1 x) (trans1 y)
trans1 (Esc e) = trans e
trans1 (Csp e) = CLift(trans e)


--}
