
import "../LangPrelude.prg" (max,otherwise,snd)

--------------------------------------------------------------------------------
-- Typed Assembly Language

data Reg :: *0 ~> *0 ~> *0 where
   ZReg :: Reg ((t,h)) t
   SReg :: (Reg h t) -> Reg ((s,h)) t
   
data Val :: *0 ~> *0 ~> *0 where
   IntVal :: Int -> Val g Int
   BoolVal :: Bool -> Val g Bool
   RegVal :: (Reg g t) -> Val g t

data Instr :: *0 ~> *0 ~> *0 ~> *0 where
   ADD :: Instr g ((Int,(Int,s))) ((Int,s))
   LEQ :: Instr g ((Int,(Int,s))) ((Bool,s))
   PUSH :: (Val g t) -> Instr g s1 ((t,s1))

data Var :: *0 ~> *0 ~> *0 where
   ZVar :: Var ((t,h)) t
   SVar :: (Var h t) -> Var ((s,h)) t
   
data Block :: *0 ~> *0 ~> *0 ~> *0 where
   Nil :: Block g s2 s2
   Cons :: (Instr g s1 s) -> (Block g s s2) -> Block g s1 s2

data Exp :: *0 ~> *0 ~> *0 where
   Int :: Int -> Exp g Int
   Bool :: Bool -> Exp g Bool
   Plus :: (Exp g Int) -> (Exp g Int) -> Exp g Int
   Lteq :: (Exp g Int) -> (Exp g Int) -> Exp g Bool
   Var :: (Var g t) -> Exp g t
   
evalInstr :: Instr g s1 s2 -> g -> s1 -> s2
evalInstr ADD      g (i,(j,stack)) = (i+j,stack)
evalInstr LEQ      g (i,(j,stack)) = (i<=j,stack)
evalInstr (PUSH v) g stack         = (evalVal v g,stack)
   
evalVal :: Val g t -> g -> t
evalVal (IntVal i)  g = i
evalVal (BoolVal b) g = b
evalVal (RegVal r)  g = evalReg r g


evalReg :: Reg g t -> g -> t
evalReg ZReg       (t,h) = t
evalReg (SReg reg) (s,h) = evalReg reg h

evalVar :: Var g t -> g -> t
evalVar ZVar       (t,h) = t
evalVar (SVar reg) (s,h) = evalVar reg h


evalBlock :: Block g s1 s2 -> g -> s1 -> s2
evalBlock Nil        g s1 = s1
evalBlock (Cons i b) g s1 = evalBlock b g (evalInstr i g s1)

append :: Block g s1 s2 -> Block g s2 s3 -> Block g s1 s3
append Nil         ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

depth :: Exp g t -> Int
depth (Int i)    = 0
depth (Bool b)   = 0
depth (Var x)    = 0
depth (Plus a b) = 1 + max (depth a) (depth b)
depth (Lteq a b) = 1 + max (depth a) (depth b)

evalExp :: Exp g t -> g -> t
evalExp (Int i)    g = i
evalExp (Bool b)   g = b
evalExp (Var x)    g = evalVar x g
evalExp (Plus a b) g = evalExp a g + evalExp b g
evalExp (Lteq a b) g = evalExp a g <= evalExp b g

----------------------------------------
-- compilation

varToReg :: Var g t -> Reg g t
varToReg ZVar     = ZReg
varToReg (SVar v) = SReg (varToReg v)

compile :: Exp g t -> Block g (t,a) b -> Block g a b
compile (Int i)    k = Cons (PUSH (IntVal i)) k
compile (Bool b)   k = Cons (PUSH (BoolVal b)) k
compile (Var x)    k = Cons (PUSH (RegVal (varToReg x))) k
-- minimize stack usage by compiling deeper sub-exp first
compile (Plus a b) k
 | depth b > depth a = compile a (compile b (Cons ADD k))
 | otherwise         = compile b (compile a (Cons ADD k))
-- can't use the same trick for non-associative LEQ
-- because LEQ doesn't have control over WHERE its operands are
compile (Lteq a b) k = compile a (compile b (Cons LEQ k))

compile1 :: Exp g t -> Block g a (t,a)
compile1 (Int i)    = Cons (PUSH (IntVal i)) Nil
compile1 (Bool b)   = Cons (PUSH (BoolVal b)) Nil
compile1 (Var x)    = Cons (PUSH (RegVal (varToReg x))) Nil
compile1 (Plus a b) = append (compile1 a) (append (compile1 b) (Cons ADD Nil))
compile1 (Lteq a b) = append (compile1 a) (append (compile1 b) (Cons LEQ Nil))

data Cmd g
  = forall t . Set (Var g t) (Exp g t) 
  |            Seq (Cmd g) (Cmd g) 
  |            If (Exp g Bool) (Cmd g) (Cmd g)
  |            While (Exp g Bool) (Cmd g) 
  | forall t . Declare (Exp g t) (Cmd (t,g))

update :: Var s t -> t -> s -> s
update ZVar     t (x,y) = (t,y)
update (SVar v) t (x,y) = (x,update v t y)

evalCmd :: Cmd g -> g -> g
evalCmd (Set v e) s             = update v (evalExp e s) s
evalCmd (Seq x y) s             = evalCmd y (evalCmd x s)
evalCmd (If test x1 x2) s       = if evalExp test s
                                   then evalCmd x1 s
                                   else evalCmd x2 s
evalCmd (While test body) s     = loop s
  where loop s = if evalExp test s
                   then loop (evalCmd body s) 
                   else s
evalCmd (Declare e body) s      = snd (evalCmd body (evalExp e s,s))


----------------------------------------
-- sample programs

{-
##test "Bad kind of type var in subFreshNames: _11667"
 bad = evalCmd prog (34,(12,1))
  where
   sum = ZVar
   x   = SVar ZVar
   prog :: Cmd (Int,(Int,a))
   prog = 
     Seq (Set sum (Int 0))
         (Seq (Set x (Int 1))
         (While (Lteq (Var x) (Int 5))
                (Seq (Set sum (Plus (Var sum)(Var x)))
                     (Set x (Plus (Var x) (Int 1))))))
-}

ok = evalCmd prog (34,(12,1))
  where
   sum = ZVar
   x   = SVar ZVar
--   prog :: Cmd (Int,(Int,a))
   prog = 
     Seq (Set sum (Int 0))
         (Seq (Set x (Int 1))
         (While (Lteq (Var x) (Int 5))
                (Seq (Set sum (Plus (Var sum)(Var x)))
                     (Set x (Plus (Var x) (Int 1))))))

