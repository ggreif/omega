import "../src/LangPrelude.prg" (Monad,maybeM,Eq,Atom,same,id,compose)

monad maybeM

--------------------------------------------------------------------------------
-- Natural Number kind Nat, and singleton data Nat' are predefined

-- kind Nat = Z | S Nat
-- data Nat':: Nat -> *0 where { Z :: Nat' Z; S:: Nat' n -> Nat' (S n)}

--------------------------------------------------------------------------------
-- Simple Type Representation

data Rep :: *0 ~> *0 where
   RInt :: Rep Int
   RBool :: Rep Bool
   RPair :: (Rep a) -> (Rep b) -> Rep ((a,b))
   Poly :: (Atom t) -> Rep t

equalRep :: Rep t -> Rep s -> Maybe (Equal s t)
equalRep RInt        RInt          = Just Eq
equalRep RBool       RBool         = Just Eq
equalRep (RPair a b) (RPair a' b') = case (equalRep a a',equalRep b b') of
                                        (Just Eq,Just Eq) -> Just Eq
                                        _ -> Nothing
equalRep _ _ = Nothing

--------------------------------------------------------------------------------
-- Typed Assembly Language

data Instr g1 g2
        = forall src tgt .
          ADD    (Val g1 Int)   -- Reg[tgt] := Reg[src] + v
                 (Reg src g1 Int)
                 (Reg tgt g2 Int)
                 (Update tgt g1 g2 Int)
        | forall src tgt .
          LEQ    (Val g1 Int)   -- Reg[tgt] := Reg[src] `lesseq` v
                 (Reg src g1 Int)
                 (Reg tgt g2 Bool)
                 (Update tgt g1 g2 Bool)
        | forall t tgt .
          LOAD   (Val g1 t)     -- Reg[tgt] := val
                 (Reg tgt g2 t)
                 (Update tgt g1 g2 t)

----------------------------------------
-- instruction sequence

data Block :: *0 ~> *0 ~> *0 where
   HALT :: Block g2 g2
   Cons :: (Instr g1 g) -> (Block g g2) -> Block g1 g2

----------------------------------------

data Val :: *0 ~> *0 ~> *0 where
   IntVal :: Int -> Val g Int
   BoolVal :: Bool -> Val g Bool
   RegVal :: (Reg n g t) -> Val g t
   Code :: (Block h1 h2) -> Val g (Block h1 h2)

----------------------------------------

data Reg :: Nat ~> *0 ~> *0 ~> *0 where
   SReg :: (Reg m h t) -> Reg (S m) ((s,h)) t
   ZReg :: Reg Z ((t,h)) t
----------------------------------------

-- (Update n g1 g2 t) g2 results from updating g1
data Update :: Nat ~> *0 ~> *0 ~> *0 ~> *0 where  
   SUpd :: (Update m h1 h2 t) -> Update (S m) ((s,h1)) ((s,h2)) t
   ZUpd :: Update Z ((s,h)) ((t,h)) t

----------------------------------------

data Weaken :: *0 ~> *0 ~> *0 where
   Drop :: (Weaken g1 h2) -> Weaken g1 ((t,h2))
   Same :: (Weaken h1 h2) -> Weaken ((t,h1)) ((t,h2))
   Empty :: Weaken g2 g2
   
--------------------------------------------------------------------------------
-- WHILE LANGUAGE

data Var :: *0 ~> *0 ~> *0 where
   ZVar :: Var ((t,h)) t
   SVar :: (Var h t) -> Var ((s,h)) t

data Exp :: *0 ~> *0 ~> *0 where
   Int :: Int -> Exp g Int
   Bool :: Bool -> Exp g Bool
   Plus :: (Exp g Int) -> (Exp g Int) -> Exp g Int
   Lteq :: (Exp g Int) -> (Exp g Int) -> Exp g Bool
   Var :: (Var g t) -> Exp g t
   Shift :: (Exp h t) -> Exp ((s,h)) t
   
data Cmd:: *0 ~> *0 where
  Set:: (Var g t) -> (Exp g t) -> Cmd g
  Seq:: (Cmd g) -> (Cmd g) -> Cmd g
  If:: (Exp g Bool) -> (Cmd g) -> (Cmd g) -> (Cmd g)
  While:: (Exp g Bool) -> (Cmd g) -> Cmd g
  Declare:: (Exp g t) -> (Cmd (t,g)) -> Cmd g

update :: Var s t -> t -> s -> s
update ZVar     t (x,y) = (t,y)
update (SVar v) t (x,y) = (x,update v t y)

eval :: Exp s t -> s -> t
eval (Int n)    s = n
eval (Bool b)   s = b
eval (Plus x y) s = (eval x s) + (eval y s)
eval (Lteq x y) s = (eval x s) <= (eval y s)
eval (Var v)    s = evalVar v s

evalVar :: Var g t -> g -> t
evalVar (ZVar)   (x,y) = x
evalVar (SVar v) (x,y) = evalVar v y

exec :: Cmd g -> g -> g
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

----------------------------------------
-- sample programs

sum = ZVar
x = SVar ZVar

prog :: Cmd (Int,(Int,a))
prog = 
 Seq (Set sum (Int 0))
     (Seq (Set x (Int 1))
     (While (Lteq (Var x) (Int 5))
            (Seq (Set sum (Plus (Var sum)(Var x)))
                 (Set x (Plus (Var x) (Int 1))))))
{-      sum = 0 ;
        x = 1;
        while (x <= 5) {
          sum = sum + x;
          x = x + 1;
        }
-}

ans = exec prog (34,(12,1))

----------------------------------------
-- compiler

data SomeReg g t = forall n . SomeReg (Reg n g t) (Nat' n)

compileVar :: Var g t -> SomeReg g t
compileVar ZVar     = SomeReg ZReg Z
compileVar (SVar v) = case compileVar v of 
                        SomeReg r m -> SomeReg (SReg r) (S m)


mkUpd :: Reg n g2 t -> Rep g1 -> Rep g2 -> Maybe (Update n g1 g2 t)
mkUpd ZReg (RPair rs rh) (RPair rt rh') = do
            Eq <- equalRep rh rh'
            return ZUpd
mkUpd (SReg r) (RPair rs rg) (RPair rs' rh) = do
            Eq <- equalRep rs rs'
            upd <- mkUpd r rg rh
            return (SUpd upd)

compileExp :: Exp g1 t -> Reg n g2 t ->
                Rep g1 -> Rep t -> Rep g2 ->
                  Maybe (Block g1 g2)

compileExp (Int i) reg ra rt rb = do
     upd <- mkUpd reg ra rb
     return (Cons (LOAD (IntVal i) reg upd)
             HALT)
compileExp (Bool b) reg ra rt rb = do
     upd <- mkUpd reg ra rb
     return (Cons (LOAD (BoolVal b) reg upd)
             HALT)

f :: Rep g1 -> Rep g2 -> Maybe(Exp g1 t -> Exp g2 t)
f (Poly x) (Poly y) = do { Eq <- same x y; return id }
f (Poly x) (RPair a b) = do { g <- f (Poly x) b; return(Shift . g) }
f x y = do { Eq <- equalRep x y; return id }
f _ _ = Nothing     

{-
compileExp (Plus a b) reg ra RInt rb = 
    do { x1 <- compileExp a reg ra RInt (RPair RInt rb)
       ; check undefined 
       }
        
        check(compileExp (Shift b) (SReg reg) (RPair RInt rb) RInt (RPair RInt rb))
        undefined
-}
