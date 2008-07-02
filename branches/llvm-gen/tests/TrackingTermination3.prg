
data Termination :: *1 where
   Total:: Termination
   Partial:: Termination

lub:: Termination ~> Termination ~> Termination
{lub Total x} = x
{lub Partial x} = Partial

data Stage :: *1 where
  Succ :: Stage ~> Stage
  Inf :: Stage
  
data Typ :: *1 where
  Arr:: Typ ~> Termination ~> Typ ~> Typ
  L:: Stage ~> Typ ~> Typ
  I:: Typ
  P:: Typ ~> Typ ~> Typ

mean:: Typ ~> *0
{mean I} = Int
{mean (Arr a n b)} = {mean a} -> {mean b}
{mean (L n a)} = [{mean a}]
{mean (P x y)} = ({mean x},{mean y})

data Prim:: Typ ~> *0 where
  Add :: Prim (Arr I Total (Arr I Total I))
  Sub :: Prim (Arr I Total (Arr I Total I))
  Mul :: Prim (Arr I Total (Arr I Total I))
  Div :: Prim (Arr I Total (Arr I Partial I))

data DBindex:: Tag ~> Typ ~> Row Tag Typ ~> *0 where
  DBz :: DBindex a t (RCons a t r)
  DBs :: DBindex a t g -> DBindex a t (RCons c b g)
 deriving Nat(d)
 
data Exp:: Typ ~> Row Tag Typ ~> Termination ~> *0 where
  Var:: Label a -> DBindex a t g -> Exp t g Total
  Shift:: Exp t g m -> Exp t (RCons a b g) m
  Const:: Int -> Exp I g Total
  Oper:: Prim t -> Exp t g Total 
  Pair:: Exp x g m -> Exp y g n -> Exp (P x y) g {lub m n}
  App:: Exp (Arr x m b) g n -> Exp x g p -> Exp b g {lub m {lub n p}}
  Cons:: Exp a g n -> Exp (L s a) g m -> Exp (L (Succ s) a) g {lub m n}
  Nil:: Exp (L (Succ s) a) g Total
  Abs:: Exp rng (RCons a dom g) n -> Exp (Arr dom n rng) g Total
  Fix:: Exp b
            (RCons body (L (Succ s) a)
            (RCons f (Arr (L s a) n b) env))
            Total ->
        Exp (Arr (L Inf a) Total b) env Total 
  PFix:: Exp b
            (RCons body a
            (RCons f (Arr a n b) env))
            m ->
        Exp (Arr a Partial b) env Total           
  Case:: Exp (L (Succ s) a) env p -> 
         Exp t env n ->
         Exp t (RCons xs (L s a)(RCons x a env)) m ->
         Exp t env {lub {lub p n} m}                                

length = Fix
   (Case (Var `x 0d)
                    (Const 0)
                    (App (App (Oper Add) (Const 1))
                         (App (Var `f 3d) (Var `ys 0d)))
               )

eval :: Exp t env Total -> Rec env -> {mean t}                          