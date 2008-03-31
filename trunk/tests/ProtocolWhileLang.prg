kind State = Open | Closed

data V :: *0 ~> *0 ~> *0 where
   Zv :: V ((t,st)) t
   Sv :: (V st t) -> V ((t1,st)) t

data Exp :: *0 ~> *0 ~> *0 where
   Int :: Int -> Exp s Int
   Bool :: Bool -> Exp s Bool
   Plus :: (Exp s Int) -> (Exp s Int) -> Exp s Int
   Lteq :: (Exp s Int) -> (Exp s Int) -> Exp s Bool
   Var :: (V s t) -> Exp s t
   
data Com :: *0 ~> State ~> State ~> *0 where
   Set :: (V st t) -> (Exp st t) -> Com st y y
   Seq :: (Com st x a) -> (Com st a y) -> Com st x y
   If :: (Exp st Bool) -> (Com st x y) -> (Com st x y) -> Com st x y
   While :: (Exp st Bool) -> (Com st y y) -> Com st y y
   Declare :: (Exp st t) -> (Com ((t,st)) x y) -> Com st x y
   Open :: Com st Closed Open
   Close :: Com st Open Closed
   Write :: (Exp st Int) -> Com st Open Open


update :: (V s t) -> t -> s -> s
update Zv n (x,y) = (n,y)
update (Sv v) n (x,y) = (x,update v n y)

eval :: Exp s t -> s -> t
eval (Int n) s = n
eval (Bool b) s = b
eval (Plus x y) s = (eval x s) + (eval y s)
eval (Lteq x y) s = (eval x s) <= (eval y s)
eval (Var Zv) (x,y) = x
eval (Var (Sv v)) (x,y) = eval (Var v) y

exec :: (Com st x y) -> st -> ([Int],st)
exec (Set v e) s = ([],update v (eval e s) s)
exec (Seq x y) s = (xs++ys,s2)
  where (xs,s1) = (exec x s)
        (ys,s2) = (exec y s1)
exec (If test x1 x2) s =
  if (eval test s) then exec x1 s else exec x2 s
exec (While test body) s = loop ([],s)
  where loop (xs,s) = 
          if (eval test s) 
             then case (exec body s) of
                   (ys,s2) -> loop (xs++ys,s2)
             else (xs,s)
exec (Declare e body) s = (xs,store)
  where (xs,(_,store)) = (exec body (eval e s,s))
exec Open s = ([],s)
exec Close s = ([],s)
exec (Write e) s = ([eval e s],s)

sum = Zv
x = Sv Zv

prog2 :: Com (Int,(Int,a)) Open Open
prog2 = 
 Seq (Set sum (Int 0))
     (Seq (Set x (Int 1))
     (While (Lteq (Var x) (Int 5))
            (Seq (Set sum (Plus (Var sum)(Var x)))
            (Seq (Write (Var x))
                 (Set x (Plus (Var x) (Int 1)))))))
            
prog :: Com (Int,(Int,a)) u u          
prog =
 Seq (Set sum (Int 0))
     (Seq (Set x (Int 1))
     (While (Lteq (Var x) (Int 5))
            (Seq (Set sum (Plus (Var sum)(Var x)))
                 (Set x (Plus (Var x) (Int 1))))))
           

ans = exec prog (34,(12,1))                   

{-
{ sum = 0 ;
  x = 1;
  while (x <= 5)
  { sum = sum + x;
    write x;
    x = x + 1;
  }
}        
-}
