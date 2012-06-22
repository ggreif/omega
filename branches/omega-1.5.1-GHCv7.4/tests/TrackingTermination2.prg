-----------------------------------------------------
-- Prelude-like functions

data Arr a m b = Arr (a -> b)

apply :: Arr a c d -> a -> d
apply (Arr f) x = f x

maybeM = Monad Just bind fail
  where fail s = Nothing
        bind Nothing g = Nothing
        bind (Just x) g = g x   

monad maybeM

data Rec :: Row Tag *0 ~> *0 where
  RNil :: Rec RNil
  RCons :: Label a -> b -> Rec r -> Rec (RCons a b r)
 deriving Record()

----------------------------------------------------------
-- New kinds and operations on them 

kind Set = Univ | Empty Tag | Times Set Set | Plus Set Set 
kind Termination = Total | Partial

lub:: Termination ~> Termination ~> Termination
{lub Total x} = x
{lub Partial x} = Partial

allU:: Set ~> Termination
{allU Univ} = Total
{allU (Empty a)} = Partial
{allU (Times x y)} = {lub {allU x} {allU y}}
{allU (Plus x y)} =  {lub {allU x} {allU y}}

union:: Set ~> Set ~> Set
{union Univ a} = Univ
{union (Times p1 p2) (Times q1 q2)} = Times {union p1 q1} {union p2 q2}
{union (Times a b) (Empty c)} = Times a b
{union (Times a b) Univ} = Univ
{union (Plus p1 p2) (Plus q1 q2)} = Plus {union p1 q1} {union p2 q2}
{union (Plus p1 p2) (Empty c)} = Plus p1 p2
{union (Plus p1 p2) Univ} = Univ
{union (Empty a) x} = x

------------------------------------------------------------
-- Judgements for well-typed patterns and terms

data Prim:: *0 ~> *0 where
  Add :: Prim (Arr Int Total (Arr Int Total Int))
  Sub :: Prim (Arr Int Total (Arr Int Total Int))
  Mul :: Prim (Arr Int Total (Arr Int Total Int))
  Div :: Prim (Arr Int Total (Arr Int Partial Int))
  
data Pat:: Set ~> *0 ~> Row Tag *0 ~> Row Tag *0 ~> *0 where
  Pvar :: Label a -> Pat Univ t r (RCons a t r)
  Ppair:: Pat s1 a g1 g2 -> Pat s2 b g2 g3 -> 
          Pat (Times s1 s2) (a,b) g1 g3
  Pwild:: Pat Univ t r r
  Pnil :: Pat (Plus Univ (Empty `Cons)) [a] r r 
  Pcons:: Pat s1 a g1 g2 -> Pat s2 [a] g2 g3 -> 
          Pat (Plus (Empty `Nil) (Times s1 s2)) [a] g1 g3
          

          
data Exp:: *0 ~> Row Tag *0 ~> Termination ~> *0 where
  Var:: Label a -> Exp t (RCons a t r) Total
  Shift:: Exp t g m -> Exp t (RCons a b g) m
  Const:: Int -> Exp Int g Total
  Oper:: Prim t -> Exp t g Total
  Pair:: Exp x g m -> Exp y g n -> Exp (x,y) g {lub m n}
  App:: Exp (Arr x m b) g n -> Exp x g p -> Exp b g {lub m {lub n p}}
  Abs:: Clause xx (Arr a i b) g1 -> Exp (Arr a {lub {allU xx} i} b) g1 Total
  Nil:: Exp [a] g Total
  Cons:: Exp a g m -> Exp [a] g n -> Exp [a] g {lub m n}
  Undefined:: Exp a g Partial
  Letrec :: Label f -> 
            Exp (Arr a Partial b) (RCons f (Arr a Partial b) r) m ->
            Exp c (RCons f (Arr a Partial b) r) n ->
            Exp c r {lub m n} 
  Cata :: Exp (Arr a m1 (Arr b m2 b)) r m3 ->
          Exp b r m4 ->
          Exp [a] r m5 ->
          Exp b r {lub m1 {lub m2 {lub m3 {lub m4 m5}}}}
          
data Clause:: Set ~> *0 ~> Row Tag *0 ~> *0 where
  Last:: (Pat s1 a g1 g2,Exp b g2 m) -> Clause s1 (Arr a m b) g1
  Next:: (Pat s1 a g1 g2,Exp b g2 m) -> 
         Clause s (Arr a n b) g1 -> 
         Clause {union s1 s} (Arr a {lub m n} b) g1 

---------------------------------------------------------------
-- evaluation for well-typed terms

liftOp f = Arr (\ x -> Arr (\ y -> f x y))

evalOp :: Prim t -> t
evalOp Add = liftOp (+)
evalOp Sub = liftOp (-)
evalOp Mul = liftOp (*)
evalOp Div = liftOp div


eval :: Exp t r m -> Rec r -> t
eval (Var a) (RCons b v r) = v
eval (Shift x) (RCons b v r) = eval x r
eval (Const n) r = n
eval (Oper p) r = evalOp p
eval (Pair x y) r = (eval x r, eval y r)
eval (App f x) r = apply (eval f r) (eval x r)
eval (Abs cl) r = Arr (evalClause cl r)
eval Nil r = []
eval (Cons x xs) r = (eval x r):(eval xs r)
eval Undefined r = error "Undefined"
eval (Letrec f fun body) r = 
  let r2 = RCons f (eval fun r2) r
  in eval body r2
eval (Cata phi base x) r = 
   let phi' = eval phi r
       base' = eval base r
       cata [] = base'
       cata (x:xs) = phi' `apply` x `apply` (cata xs)
    in cata (eval x r)

evalPat :: Pat s t g1 g2 -> t -> Rec g1 -> Maybe (Rec g2)
evalPat (Pvar s) v r = return(RCons s v r)
evalPat (Ppair p q) (x,y) r = 
  do { r1 <- evalPat p x r; evalPat q y r1}
evalPat (Pwild {- m -} ) v r = return r
evalPat Pnil [] r = return r
evalPat Pnil (x:xs) r = Nothing
evalPat (Pcons x y) (z:zs) r = 
  do { r1 <- evalPat x z r; evalPat y zs r1}
evalPat (Pcons x y) [] r1 = Nothing

evalClause :: Clause s (Arr a m b) g1 -> Rec g1 -> (a -> b)
evalClause (Next (p,e) m) r v =
  case evalPat p v r of
    Nothing -> evalClause m r v
    Just r2 -> eval e r2
evalClause (Last (p,e)) r v =
  case evalPat p v r of
    Nothing -> error "Pattern Match Failure"
    Just r2 -> eval e r2  

--------------------------------------------------
-- Some examples

c1 = (Pnil,Const 0)
c2 = (Pcons (Pvar `x) Pwild,Var `x)
c3 = (Pwild, Undefined)
c4 = (Pcons (Pvar `x) (Pcons (Pvar `y) (Pvar `ys)),Shift(Shift(Var `x)))

d1 = Next c1 (Last c2)
d2 = Next c2 (Last c3)
d3 = Last c2
d4 = Last c3
d5 = Next c1 (Last c4)
d6 = Next c2 d5

-- abs :: Label a -> Exp b (RCons (Has a c) d) e -> Exp (Arr c e b) d f
abs x e = Abs(Last (Pvar x,e))

add x y = App (App (Oper Add) x) y
times x y = App (App (Oper Mul) x) y
sub x y = App (App (Oper Sub) x) y

-- let `f = (\ `x -> (1 + ((Sh `f) `x)))
-- in (`f 3)
zz:: Exp Int g Partial
zz = 
  Letrec `f (abs `x (App (App (Oper Add) (Const 1))
                         (App (Shift (Var `f)) (Var `x))))
            (App (Var `f) (Const 3))

-- let `length = (\ [] -> 0
--                  (`x:`xs) -> (1 + ((Sh (Sh `length)) `xs)))
-- in `length
length1 :: Exp (Arr [a] Partial Int) b Total
length1 = Letrec `length (Abs (Next (Pnil,Const 0)
                              (Last (Pcons (Pvar `x) (Pvar `xs),
                                     add (Const 1)
                                          (App (Shift(Shift(Var `length))) 
                                               (Var `xs))))))
                         (Var `length)                                               

          
-- \ [] -> 0
--   (`x:_) -> `x
t1x :: Exp (Arr [Int] Total Int) a Total
t1x = Abs d1
 
 
-- \ (`x:_) -> `x
--   _ -> undefined
t2x :: Exp (Arr [a] Partial a) b Total
t2x = Abs d2

---- This should fail 
##test "Unifier shows too polymorphic"
  t2xBad :: Exp (Arr [a] c a) b Total
  t2xBad = Abs d2  

-- \ (`x:_) -> `x
t3x :: Exp (Arr [a] Partial a) b Total
t3x = Abs d3


-- \ _ -> undefined
t4x :: Exp (Arr a Partial b) c Total
t4x = Abs d4


-- \ [] -> 0
--   (`x:(`y:`ys)) -> (Sh (Sh `x))
t5x :: Exp (Arr [Int] Partial Int) a Total
t5x = Abs d5


-- \ (`x:_) -> `x
--   [] -> 0
--   (`x:(`y:`ys)) -> (Sh (Sh `x))
t6x :: Exp (Arr [Int] Total Int) a Total
t6x = Abs d6


-- \ `f -> \ `g -> \ `x -> ((Sh (Sh `f)) ((Sh `g) `x))
  
-- compose :: Exp (Arr (Arr a b c) d (Arr (Arr e b a) f (Arr e b c))) g h
compose = abs `f (abs `g (abs `x (App (Shift(Shift (Var `f))) (App (Shift (Var `g)) (Var `x)))))


-- \ x -> \ y -> Add y 1
succ = abs `x (abs `y (App (App (Oper Add) (Var `y)) (Const 1)))

length :: Exp (Arr [a] Total Int) g Total
length = 
   abs `x (Cata succ
                (Const 0) 
                (Var `x))

xs = Cons (Const 1) (Cons (Const 3) (Cons (Const 5) Nil))

-------------------------------------------------
-- printing terms

sp :: Pat a b c d -> String
sp (Pvar s) = show s
sp (Ppair x y) = "("++sp x++","++sp y++")"
sp Pwild = "_"
sp Pnil = "[]"
sp (Pcons x xs) = "("++sp x++":"++sp xs++")"

sc :: Clause a b c -> String
sc (Last(p,e)) = sp p++" -> "++se e
sc (Next (p,e) cs) = sp p++" -> "++se e++"\n--   "++sc cs

se :: Exp a b c -> String
se (Var x) = show x
se (Shift x) = "(Sh "++se x++")"
se (Const n) = show n
se (Pair x y) = "("++se x++","++se y++")"
se (App (App (Oper f) x) y) = "("++se x++so f++se y++")"
se (App x y) = "("++se x++" "++se y++")"
se (Abs cl) = "(\\ "++sc cl++")"
se Nil = "[]"
se (Cons x xs) = "("++se x++":"++se xs++")"
se Undefined = "undefined"
se (Letrec f x y) = 
  "-- let "++show f++" = "++se x++"\n   in "++se y++"\n"
se (Oper Add) = "(+)"
se (Oper Sub) = "(-)"
se (Oper Mul) = "(*)"
se (Oper Div) = "div"
se (Cata phi b xs) = "(cata "++se phi++" "++se b++" "++se xs++")"

so :: Prim t -> String 
so Add = " + "
so Sub = " - "
so Mul = " * "
so Div = " / "

f x = putStr ("\n"++(se x)++"\n")
