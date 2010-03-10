
-- kind Nat = Z | S Nat

--data N t = Zero where t = Z | ex x.Succ (N x) where t = S x
data N :: Nat ~> *0 where
   Zero :: N Z
   Succ :: (N x) -> N (S x)
   
data Range n m = Range (N n) (N m)

range1 = Range Zero (Succ (Succ Zero))

one = Num (Succ Zero)
two = Num (Succ (Succ Zero))

onePlusOne :: Add (S Z) (S Z) (S (S Z))
onePlusOne = Step Base

onePlusTwo :: Add (S Z) (S (S Z)) (S (S (S Z)))
onePlusTwo = Step Base

-- 1 + 2
ex1 = Plus onePlusTwo onePlusTwo one two

data Add :: Nat ~> Nat ~> Nat ~> *0 where
   Base :: Add Z z z
   Step :: (Add a y b) -> Add (S a) y (S b)

data Ty :: *0 ~> *0 where
   Bool :: Ty Bool
   Rng :: (Range n m) -> Ty (Range n m)
   Pair :: (Ty a) -> (Ty b) -> Ty ((a,b))
   Sum :: (Ty a) -> (Ty b) -> Ty ((a+b))
   Arr :: (Ty a) -> (Ty b) -> Ty (a -> b)

data Var :: *0 ~> *0 ~> *0 where
   Vz :: Var ((t,e2)) t
   Vs :: (Var e2 t) -> Var ((t2,e2)) t

data Exp :: *0 ~> *0 ~> *0 where
   Num :: (N n) -> Exp e (Range n n)
   Bconst :: Bool -> Exp e Bool
   Tick :: (Exp e t) -> Exp e t
   Var :: (Var e t) -> Exp e t
   Prod :: (Exp e a) -> (Exp e b) -> Exp e ((a,b))
   Disj :: (Exp e a) -> (Exp e b) -> Exp e ((a+b))
   Lam :: (Exp ((a,e)) b) -> Exp e (a -> b)
   App :: (Exp e (a -> t)) -> (Exp e a) -> Exp e t
   Plus :: (Add m p i) -> (Add n q j) -> (Exp e (Range m n)) -> 
           (Exp e (Range p q)) -> Exp e (Range i j)
   BoolOp :: BoolOp -> (Exp e Bool) -> (Exp e Bool) -> Exp e Bool
   RelOp :: RelOp -> (Exp e (Range m n)) -> (Exp e (Range p q)) -> Exp e Bool
   
data BoolOp = And | Or | Not | Implies
data RelOp = EQ' | LT' | GT' | NE' | LTE' | GTE'

data Defs :: *0 ~> *0 where
   First :: (Ty t) -> (Exp e t) -> Defs e
   Cons :: (Ty t) -> (Exp e2 t) -> (Defs e2) -> Defs (t,e2)
   
data Prog e = Prog (Ty e)(Defs e)(Exp e Bool)
                   (Exp e Bool) (Exp e Bool) (Exp e Bool)

init (Prog env ds a b c d) = a
next (Prog env ds a b c d) = b
invariant (Prog env ds a b c d) = c
final (Prog env ds a b c d) = d
