kind Domain = High | Low

data D :: Domain ~> *0 where
   Lo :: D Low
   Hi :: D High

data P x y = P

data V :: *0 ~> Domain ~> *0 ~> *0 where
   Zv :: (D d) -> V (P (D d,d0) (t,s0)) d t
   Sv :: (V (P a b) d t) -> V (P ((d1,a)) ((t1,b))) d t
 
data Dless :: Domain ~> Domain ~> *0 where
   LH :: Dless Low High
   LL :: Dless Low Low
   HH :: Dless High High
   
data Exp :: *0 ~> Domain ~> *0 ~> *0 where
   Int :: Int -> Exp s d Int
   Bool :: Bool -> Exp s d Bool
   Plus :: (Exp s d Int) -> (Exp s d Int) -> Exp s d Int
   Lteq :: (Exp s d Int) -> (Exp s d Int) -> Exp s d Bool
   Var :: (V s d2 t) -> (Dless d2 d) -> Exp s d t
   
data Com :: Domain ~> *0 ~> *0 where
   Set :: (V st d2 t) -> (Exp st d1 t) -> (Dless d1 d2) -> (Dless d d2) -> Com d st
   Seq :: (Com d st) -> (Com d st) -> Com d st
   If :: (Exp st d Bool) -> (Com d st) -> (Com d st) -> Com d st
   While :: (Exp st d Bool) -> (Com d st) -> Com d st
   Declare :: (D d2) -> (Exp (P a b) d2 t) -> (Com d (P ((D d2,a)) ((t,b)))) -> Com d (P a b)



update :: (V (P a s) d t) -> t -> s -> s
update (Zv d) n (x,y) = (n,y)
update (Sv v) n (x,y) = (x,update v n y)

eval :: Exp (P a s) d t -> s -> t
eval (Int n) s = n
eval (Bool b) s = b
eval (Plus x y) s = (eval x s) + (eval y s)
eval (Lteq x y) s = (eval x s) <= (eval y s)
eval (Var (Zv d) _) (x,y) = x
eval (Var (Sv v) p) (x,y) = eval (Var v p) y


exec :: (Com d (P a st)) -> st -> st
exec (Set v e _ _) s = update v (eval e s) s
exec (Seq x y) s = exec y (exec x s)
exec (If test x1 x2) s =
  if (eval test s) then exec x1 s else exec x2 s
exec (While test body) s = loop s
  where loop s = if (eval test s) 
                    then loop (exec body s) 
                    else s
exec (Declare d e body) s = store
  where (_,store) = (exec body (eval e s,s))

sum = (Zv Hi)
x = Sv (Zv Lo)
y = Sv (Zv Hi)

prog :: Com Low (P (D High,(D Low,a)) (Int,(Int,b)))
prog = 
 Seq (Set sum (Int 0) HH LH)
     (Seq (Set x (Int 1) LL LL)
     (While (Lteq (Var x LL) (Int 5))
            (Seq (Set sum (Plus (Var sum HH)(Var x LH)) HH LH)
                 (Set x (Plus (Var x LL) (Int 1)) LL LL))))

{-                 
ans = exec prog (34,(12,1))                   

{-
{ sum = 0 ;
  x = 1;
  while (x <= 5)
  { sum = sum + x;
    x = x + 1;
  }
}        
-}
-}
