
data Termination :: *1 where
   Total:: Termination
   Partial:: Termination

lub:: Termination ~> Termination ~> Termination
{lub Total x} = x
{lub Partial x} = Partial

data Stage :: *1 where
  Succ :: Stage ~> Stage
  Inf :: Stage
 deriving syntax(s) Tick(Succ)

data Typ :: *1 where
  Arr:: Typ ~> Termination ~> Typ ~> Typ
  Li :: Stage ~> Typ ~> Typ
  I:: Typ
  P:: Typ ~> Typ ~> Typ
 deriving syntax(ty) Pair(P)

mean:: Typ ~> *0
{mean I} = Int
{mean (Arr a n b)} = {mean a} -> {mean b}
{mean (Li n a)} = [{mean a}]
{mean (x, y)ty} = ({mean x},{mean y})

data Prim:: Typ ~> *0 where
  Add :: Prim (Arr I Total (Arr I Total I))
  Sub :: Prim (Arr I Total (Arr I Total I))
  Mul :: Prim (Arr I Total (Arr I Total I))
  Div :: Prim (Arr I Total (Arr I Partial I))

data DBindex:: Tag ~> Typ ~> Row Tag Typ ~> *0 where
  DBz :: DBindex a t {a=t; r}r
  DBs :: DBindex a t g -> DBindex a t {c=b; g}r
 deriving Nat(d)

data Exp:: Typ ~> Row Tag Typ ~> Termination ~> *0 where
  Var:: Label a -> DBindex a t g -> Exp t g Total
  Shift:: Exp t g m -> Exp t {a=b; g}r m
  Const:: Int -> Exp I g Total
  Oper:: Prim t -> Exp t g Total 
  Pair:: Exp x g m -> Exp y g n -> Exp (x, y)ty g {lub m n}
  App:: Exp (Arr x m b) g n -> Exp x g p -> Exp b g {lub m {lub n p}}
  Cons:: Exp a g n -> Exp (Li s a) g m -> Exp (Li (s`1)s a) g {lub m n}
  Nil:: Exp (Li (s`1)s a) g Total
  Abs:: Exp rng {a=dom; g}r n -> Exp (Arr dom n rng) g Total
  Fix:: Exp b {body=Li (s`1)s a, f=Arr (Li s a) n b; env}r
            Total ->
        Exp (Arr (Li Inf a) Total b) env Total 
  PFix:: Exp b {body=a, f=Arr a n b; env}r
            m ->
        Exp (Arr a Partial b) env Total           
  Case:: Exp (Li (s`1)s a) env p -> 
         Exp t env n ->
         Exp t {xs=Li s a, x=a; env}r m ->
         Exp t env {lub {lub p n} m}                                

length = Fix
   (Case (Var `x 0d)
                    (Const 0)
                    (App (App (Oper Add) (Const 1))
                         (App (Var `f 3d) (Var `ys 0d)))
               )

eval :: Exp t env Total -> Rec env -> {mean t}                          
