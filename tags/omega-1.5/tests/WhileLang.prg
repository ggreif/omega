import "../src/LangPrelude.prg" (Monad,maybeM,fst,snd)

monad maybeM

succeed = return

----------------------------------------------
data V :: *0 ~> *0 ~> *0 where
   Zv :: V ((t,m)) t
   Sv :: (V m t) -> V ((x,m)) t
  
data Exp :: *0 ~> *0 ~> *0 where
   IntC :: Int -> Exp s Int
   BoolC :: Bool -> Exp s Bool
   Plus :: (Exp s Int) -> (Exp s Int) -> Exp s Int
   Lteq :: (Exp s Int) -> (Exp s Int) -> Exp s Bool
   Var :: (V s t) -> Exp s t
      
data Com:: *0 ~> *0 where
  Set:: V s t -> Exp s t -> Com s              -- x := e                
  Seq:: Com s -> Com s -> Com s                -- { s1; s2; }           
  If:: Exp s Bool -> Com s -> Com s -> Com s   -- if e then x else y    
  While:: Exp s Bool -> Com s -> Com s         -- while e do s          
  Declare:: Exp s t -> Com (t,s) -> Com s      -- { int x = 5; s }      

update :: (V s t) -> t -> s -> s
update Zv n (x,y) = (n,y)
update (Sv v) n (x,y) = (x,update v n y)

eval :: Exp s t -> s -> t
eval (IntC n) s = n
eval (BoolC b) s = b
eval (Plus x y) s = (eval x s) + (eval y s)
eval (Lteq x y) s = (eval x s) <= (eval y s)
eval (Var Zv) (x,y) = x
eval (Var (Sv v)) (x,y) = eval (Var v) y


exec :: (Com st) -> st -> st
exec (Set v e) s = update v (eval e s) s
exec (Seq x y) s = exec y (exec x s)
exec (If test x1 x2) s =
  if (eval test s) then exec x1 s else exec x2 s
exec (While test body) s = loop s
  where loop s = if (eval test s) 
                    then loop (exec body s) 
                    else s
exec (Declare e body) s = store
  where (_,store) = (exec body (eval e s,s))



v0 = Zv
v1 = Sv Zv
v2 = Sv (Sv Zv)
v3 = Sv (Sv (Sv Zv))

e2 = Lteq (Plus (Var v0)(Var v1)) (Plus (Var v0) (IntC 1))
  
sum = Zv
x = Sv Zv

prog :: Com (Int,(Int,a))
prog = 
 Seq (Set sum (IntC 0))
     (Seq (Set x (IntC 1))
     (While (Lteq (Var x) (IntC 5))
            (Seq (Set sum (Plus (Var sum)(Var x)))
                 (Set x (Plus (Var x) (IntC 1))))))
                   
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

--##test "bad var"
-- ans1 = If (Var x) (Set x (IntC 0)) (Set x (IntC 1))


---------------------------------------------------
-- Untyped Annotated AST

data TyAst = I | B | P TyAst TyAst



-- Judgments for Types
data TJudgment = exists t . TJ (TypeR t)   

checkT :: TyAst -> TJudgment
checkT I = TJ IntR
checkT B = TJ BoolR
checkT (P x y) = 
   case (checkT x,checkT y) of
     (TJ a, TJ b) -> TJ(PairR a b)

----------------------------------------------------
-- Equality Proofs and Type representations
-- data Equal:: *0 ~> *0 ~> *0 where Eq:: Equal a a

data TypeR :: *0 ~> *0 where
   IntR :: TypeR Int
   BoolR :: TypeR Bool
   PairR :: (TypeR a) -> (TypeR b) -> TypeR ((a,b))
   
match :: TypeR a -> TypeR b -> Maybe (Equal a b)
match IntR IntR = succeed Eq
match BoolR BoolR = succeed Eq
match (PairR a b) (PairR c d) =
  do { Eq <- match a c
     ; Eq <- match b d
     ; succeed Eq }
match _ _ = fail "match fails"     


----------------------------------------------
-- checking Variables are consistent

checkV :: Int -> TypeR t -> TypeR s -> Maybe(V s t)
checkV 0 t1 (PairR t2 p) =
  do { Eq <- match t1 t2
     ; return Zv }
checkV n t1 (PairR ty p) = 
  do { v <- checkV (n-1) t1 p; return(Sv v)}
checkV n t1 sr = Nothing


-----------------------------------------------------
data ExpAst 
  = IntCA Int
  | BoolCA Bool
  | PlusA ExpAst ExpAst
  | LteqA ExpAst ExpAst
  | VarA Int TyAst

-- Judgments for Expressions
data EJudgment s = exists t . EJ (TypeR t) (Exp s t)  

checkE :: ExpAst -> TypeR s -> Maybe (EJudgment s)
checkE (IntCA n) sr = succeed(EJ IntR (IntC n))
checkE (BoolCA b) sr = succeed(EJ BoolR (BoolC b))
checkE (PlusA x y) sr =
  do { EJ t1 e1 <- checkE x sr
     ; Eq <- match t1 IntR
     ; EJ t2 e2 <- checkE y sr
     ; Eq <- match t2 IntR
     ; succeed(EJ IntR (Plus e1 e2))}
checkE (VarA n ty) sr = 
  do { TJ t <- succeed(checkT ty)
     ; v <- checkV n t sr 
     ; return(EJ t (Var v)) }

-----------------------------------------------------
data ComAst 
  = SetA Int TyAst ExpAst
  | SeqA ComAst ComAst
  | IfA ExpAst ComAst ComAst
  | WhileA ExpAst ComAst
  | DeclareA TyAst ExpAst ComAst

data CJudgment s = EC (Com s)

checkC :: ComAst -> TypeR s -> Maybe(CJudgment s)
checkC (SetA n ty e) sr =
  do { TJ t1 <- succeed(checkT ty)
     ; v <- checkV n t1 sr
     ; EJ t2 e1 <- checkE e sr
     ; Eq <- match t1 t2
     ; return(EC (Set v e1))}
checkC (SeqA x y) sr = 
  do { EC c1 <- checkC x sr
     ; EC c2 <- checkC y sr
     ; return(EC (Seq c1 c2)) }
checkC (IfA e x y) sr = 
  do { EJ t1 e1 <- checkE e sr
     ; Eq <- match t1 BoolR
     ; EC c1 <- checkC x sr
     ; EC c2 <- checkC y sr
     ; return(EC(If e1 c1 c2)) }
checkC (WhileA e x) sr = 
  do { EJ t1 e1 <- checkE e sr
     ; Eq <- match t1 BoolR
     ; EC c1 <- checkC x sr
     ; return(EC(While e1 c1)) }
checkC (DeclareA ty e c) sr = 
  do { TJ t1 <- succeed(checkT ty)
     ; EJ t2 e2 <- checkE e sr
     ; Eq <- match t1 t2
     ; EC c2 <- checkC c (PairR t1 sr)
     ; return(EC(Declare e2 c2)) }

--------------------------------------------------------------

e1 = Lteq (Plus (Var sum)(Var x)) (Plus (Var x) (IntC 1))

data Store :: *0 ~> *0 where
   M :: (Code s) -> Store s
   N :: (Code a) -> (Store b) -> Store ((a,b))
   

eval2 :: Exp s t -> Store s -> Code t
eval2 (IntC n) s = lift n
eval2 (BoolC b) s = lift b
eval2 (Plus x y) s = [| $(eval2 x s) + $(eval2 y s) |]
eval2 (Lteq x y) s = [| $(eval2 x s) <= $(eval2 y s) |]
eval2 (Var Zv) (N a b) = a
eval2 (Var (Sv v)) (N a b) = eval2 (Var v) b
eval2 (Var Zv) (M x) = [| fst $x |]
eval2 (Var (Sv v)) (M x) = eval2 (Var v) (M [| snd $x |])


test e = [| \ (x,(y,z)) -> $(eval2 e (N [|x|] (N [|y|] (M [|z|])))) |]

-- test e1 --->  [| \ (x,(y,z)) -> x + y <= y + 1 |]

