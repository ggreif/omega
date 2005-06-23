-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Thu Jun 23 11:51:26 Pacific Daylight Time 2005
-- Omega Interpreter: version 1.1 (revision 1)

import "LangPrelude.prg" 
  (head,tail,lookup,member,fst,snd,Monad,maybeM)

--------------------------------------------------
-- Simple non parameterized type synonyms

type IntList = [Int]

data T = CT1 Int IntList

x = CT1 5 [2,3]

##test "Kind check in Type Synonym"
  type IntList = ([] Int a)
  
-----------------------
-- tests for mutually recursive types

data T1 x = T1 [S1 x]
data S1 x = S1 x (T1 x)
test1 = T1 [S1 5 (T1 [])]

------------------------------------
-- tests for patterns

Cp :: Int -> Int -> [Int] -> ([Int],Int)
pattern Cp x y zs = (y:zs,x)

----------------------------------------------
-- simple recursive function

fact n = if n==0 then 1 else n * (fact (n-1))

-----------------------------------------------
-- Tests of mutually recursive functions

even 0 = True
even n = odd (n-1)

odd 0 = False
odd n = even (n-1)

------------------------------------------------
-- Tests of lazy pattern matching for recursive
-- value declarations, and lazy pattern matching of
-- constructor and pair based patterns

(twos,junk) = (2:(lazy twos),lazy(head twos))
(ms,ns) = (1:(lazy ns),2:(lazy ms)) 

us = 1 : (lazy ws)
ws = 2 : us

(L z1) = L 3

[x1,y1] = [2,4]

-------------------------------
-- Explicit laziness

from n =  n : (lazy (from (n+1)))

take 0 xs = []
take n [] = []
take n (x:xs) = x : take (n-1) xs

map0 f3 [] = []
map0 f3 (x:xs) = f3 x : mimic (map0 f3) xs

map1 f [] = []
map1 f (x:xs) = f x : map1 f xs

map2 f [] = []
map2 f (x:xs) = f x : (lazy (map2 f xs))


-- recursive value definitions
ones = 1 : (lazy ones)

expose 0 xs = xs
expose n [] = []
expose n (x:xs) = x : expose (n-1) xs

-- fibonocci
zipWith f (x:xs) (y:ys) = 
  f x y : mimic (mimic (zipWith f) xs) ys

fibs = 0 : 1 : (lazy (zipWith (+) fibs (tail fibs)))


-- primes
iterate f a = a : (lazy (iterate f (f a)))

filter p [] = []
filter p (x:xs) = if p x 
                     then x : mimic (filter p) xs 
                     else mimic (filter p) xs

sieve (p:xs) = filter pred xs
  where pred y = rem y p /= 0

primes = map0 head (iterate sieve (from 2))

-- DFS search tree

data Tree = Node Int [Tree]
data Graph  = G [(Int,[Int])]

expand :: Graph -> Int -> Tree
expand (G xs) root = 
       case lookup root xs of
         Just children -> 
            Node root 
                 (map0 (\ w -> lazy (expand (G xs) w)) 
                      children)

g1 = G [ (1,[2,3]),(2,[3]),(3,[4,5]),(4,[]),(5,[3]) ]

push 0 g = g
push n (Node x ys) = Node x (map0 (push (n-1)) ys)

prune :: [Int] -> [Tree] -> ([Tree],[Int])
prune visited [] = ([],visited)
prune visited ((Node n cs) : ts) = 
  if member n visited
     then prune visited ts
     else let (xs,vs) = prune (n : visited) cs
              (ys,us) = prune vs ts
          in ((Node n xs) : ys, us) 
     
     {- case (prune (n : visited) cs) of
          (xs,vs) -> case prune vs ts of 
                       (ys,us) -> ((Node n xs) : ys, us) -}     
          

dff :: Graph -> Int -> [Tree]
dff g root = fst( prune [] [expand g root] )


--------- Some tests using the definitions
incr x = x + 1

l1 = from 3                 -- [3 ...] : [Int]
l2 = take 5 (from 1)        -- [1,2,3,4,5] : [Int]
l3 = map2 incr [1,2,3]      -- [2 ...] : [Int]
l4 =  map2 incr (from 1)    -- [2 ...] : [Int]
l5 = map1 incr [1,2,3]      -- [2,3,4] : [Int]
-- l6 = map1 incr (from 1)  -- diverges
l7 =  map0 incr (from 1)     -- [2 ...] : [Int]
l8 = expose 3 ones          -- [1,1,1 ...] : [Int]
l9 = expose 5 fibs          -- [0,1,1,2,3 ...] : [Int]
l10 = take 10 primes        -- [2,3,5,7,11,13,17,19,23,29] : [Int]

l11 = expand g1 1           -- (Node 1 [ ..., ...]) : Tree
l12 = push 2 (expand g1 1)  -- (Node 1 [(Node 2 [ ...]),(Node 3 [ ..., ...])]) : Tree
l13 =  dff g1 1


l14 =  map0 (push 10) l13    -- [(Node 1 [(Node 2 [(Node 3 [(Node 4 []),(Node 5 [])])])])] : [Tree]

--------------------------------
-- building code

inc x = x + 1
c1a = [| 4 + 3 |]
c2a = [| \ x -> x + $c1a |]
c3 = [| let f x = y - 1 where y = 3 * x in f 4 + 3 |]
c4 = [| inc 3 |]

c5 = [| [| 3 |] |]
c6 = [| \ x -> x |]


c7 = (\ x -> [| \ y -> y x |]) 4
c8 = run ((\ x -> [| \ y -> y x |]) 4)
c9 = (run ((\ x -> [| \ y -> y x |]) 4)) (\ x -> x)
c10 = 3 + 4
c11 = [| \ a -> $(( \ x -> [|  x  |] ) (\ y -> [| a |]) ) 0 |]
c12 = run((run [| \ a -> $(( \ x -> [|  x  |] ) (\ y -> [| a |]) ) 0 |]) 5)

-- Is this ok? seems to run an open term [| a |]
c13 = [| (\ a -> $( (\ x -> [|  x  |] ) (\ w -> run [| a |]  )) 0) |]

c14 = (run [| (\ a -> $( (\ x -> [|  x  |]) (\ w -> run [| a |])) 0) |]) 5

c15 = let fact x = if x==0 then 1 else x * (fact (x-1)) in fact 3

c16 = let h2 n z = 
            if n==0
               then z 
               else [| (\ x -> $(h2 (n-1) [|  x + ( $z )  |] )) n  |] 
      in h2 3 [| 4 |] 
      
c17 = run c16

c18 = let h 0 z = z
          h n z = [| let y = n in $(h (n-1) [| $z + y |]) |]
      in h 3 [| 99 |] 
--------------------------------------------
-- swapping

sa = fresh 'a'
sb = fresh 'b'
sc = fresh 'c'

t1 = (3,(sa,sb),[sc])
t2 = swap sa sb t1
f3 x = (x,sa,sb)
f4 = \ x -> (x,sa,sb)
t3 = (swap sa sb f3) 7
t4 = (swap sa sb f4) 22
t5 = (swap sa sb (f4 9),(swap sa sb f4) 9)
t6 = (swap sa sb (f4 sa),(swap sa sb f4) (swap sa sb sa))
t7 = (swap sa sb (swap sa sb t1),t1)
t8 = (swap sa sb t1,swap sb sa t1)

------------------------------------------------
-- tests of the Do notation

-- should run in the Maybe monad defined in the prelude
d1 = do { x <- Just 4; return(x+1) }
  where monad maybeM

-- define and test a new State monad

data St st a = St (st -> (a,st)) 

stateM =  (Monad unit bind fail)
  where unit a = St(\ st -> (a,st))
        bind (St f) g = St h
          where h st = case f st of
                         (a,st') -> case g a of
                                      (St j) -> j st'
        fail s = error ("Fail in state monad: "++s)

runstate n (St f) = f n
        
getstate = St f
  where f s = (s,s)

setstate n = St f
  where f s = ((),n)

d2 = runstate 0 (do { setstate 4; x <- getstate; return(x+1) })
  where (Monad return bind fail) = stateM

d3 = runstate 5 (do { a <- getstate; setstate 3; x <- getstate; return(x+a) })
  where monad stateM

------------------------------------------------------------
-- tests of existential vars

data PairX x = forall t . PairX  (t -> x) t

testEx1 = PairX (\ x -> x + 1) 5

testEx2 (PairX g z) = g z

-- All of these go wrong
##test "OOps"
  x = 4 + True

##test "Var escapes into type of lambda bound var"
  g z = h c1
    where h (PairX g w) = g (hd z)
  
##test "Var escapes directly"  
  f2 (PairX g z) = g

##test "Skolem gets bound 2"
  f3 (PairX g z) = g 3

##test "Skolem gets bound 1"
  f1 (PairX g z) = z + 1

------------------------------------------------------------------
-- tests of the new equality types


data Zx = Zx
data Sx x = Sx x

data Nat1 t = IsZ where t = Zx
           | forall x . IsS x where t = Sx x



data Eq1 x y = Eq1 where x = y

testEq1 :: Eq1 (t x) (t y) -> Eq1 x y
testEq1 Eq1 = Eq1 

data Rep t =
                 Rint                  where t = Int
  |              Rchar                 where t = Char
  |              Runit                 where t = ()
  | forall a b . Rpair (Rep a) (Rep b) where t = (a,b)
  | forall a b . Rsum  (Rep a) (Rep b) where t = (+) a b
  | forall i . Rdata (Rep i) (t -> i) (i -> t)
  --| Rparam (forall a . Rep a -> Rep (t a))

list :: Rep a -> Rep [a]
list x = Rdata (Rsum Runit (Rpair x (lazy (list x)))) h g
  where h [] = L ()
        h (x:xs) = R (x,xs)
        g (L ()) = []
        g (R (x,xs)) = x:xs

sum :: Rep a -> a -> Int
sum Rint n = n
sum (Rpair r s) (x,y) = sum r x + sum s y
sum (Rsum r s) (L x) = sum r x
sum (Rsum r s) (R x) = sum s x
sum (Rdata i f g) x = sum i (f x)
sum _ x = 0



data Var e t
 = forall f.   Z2           where e = (f,t)
 | forall f a. S2 (Var f t) where e = (f,a)

 
data Exp e t 
  = Lit t
  | V (Var e t)
  | forall a b . Abs  (Exp (e,a) b)                where t = (a -> b)
  | forall a   . App  (Exp e (a->t)) (Exp e a)
  | forall a b . Pair (Exp e a) (Exp e b)          where t = (a,b)
  | forall a b . Pi1  (Exp e (a,b))                where t = a
  | forall a b . Pi2  (Exp e (a,b))                where t = b

--------------------------------------------------------------------
-- Generalize lifting to all kinds env transformations

up :: (forall t . (Var a t -> Var b t)) ->  Var (a,x) t -> Var (b,x) t
up f Z2 = Z2
up f (S2 v) = S2(f v)

lift1 :: (forall t . (Var a t -> Var b t)) -> Exp a t -> Exp b t
lift1 f (V v) = V(f v)
lift1 f (App x y) = App (lift1 f x) (lift1 f y)
lift1 f (Abs e) = Abs(lift1 (up f) e)
lift1 f (Pair x y) = Pair (lift1 f x) (lift1 f y)
lift1 f (Lit n) = Lit n
lift1 f (Pi1 x) = Pi1 (lift1 f x)
lift1 f (Pi2 x) = Pi2 (lift1 f x)

liftV :: Var e t -> Var (e,a) t
liftV Z2 = S2 Z2
liftV (S2 v) = S2(liftV v)

promote :: (forall a b c . (Exp a b) -> Exp ((a,c)) b)
promote = lift1 liftV 

demV ::  Var (e,a) t -> Var e t 
demV Z2 = error "Impossible in demote"
demV (S2 v) = v 

demote :: (forall a . Exp (e,a) b) -> Exp e b
demote = lift1 demV

--------------------------------------------------------------------

eval :: (Exp e t) -> e -> t
eval (App x y) env = (eval x env) (eval y env)
eval (Lit n) env = n
eval (Abs e) env = \ x -> eval e (env,x)
eval (V Z2) env = snd env
eval (V (S2 v)) env = eval (V v) (fst env)
eval (Pair x y) env = (eval x env, eval y env)
eval (Pi1 x) env = fst(eval x env)
eval (Pi2 x) env = snd(eval x env)

evalVar :: (Var e t) -> e -> t
evalVar Z2 e = snd e
evalVar Z2 (x,y) = y
evalVar (S2 v) e = evalVar v (fst e)
evalVar (S2 v) (x,y) = evalVar v x
 

x3 = App (Abs (V Z2)) (Lit 5)

evV :: Var e t -> e -> t
evV Z2 (x,y) = y
evV (S2 v) (x,y) = evV v x

----------------------------------------------------
----------------------------------------------------
-- Checking that facts accumulate from Left to Right

##test "Facts accumulate from left to right in clauses"
  evVar :: e -> (Var e t) -> t
  evVar (x,y) Z2 = y

evV2 :: (Var e t,e) -> t
evV2 (Z2,(x,y)) = y
evV2 (S2 v,(x,y)) = evV v x

##test "Facts accumulate from left to right in tuples"
  evV3 :: (e,Var e t) -> t
  evV3 ((x,y),Z2) = y
  evV3 ((x,y),S2 v) = evV3 (x,v) 
 
----------------------------------------- 

data Subst e = 
    Id
  | forall x a . None (Subst x) where e = (x,a)
  | forall x a . One (forall z . Exp z a) (Subst x) where e = (x,a)

subVar :: Subst e -> Var e t -> Exp e t
subVar Id v = V v
subVar (None _) Z2 = V Z2
subVar (None e) (S2 v) = promote(subVar e v)
subVar (One exp e) Z2 = exp
subVar (One exp e) (S2 v) = promote(subVar e v)

sub :: Subst e -> Exp e t -> Exp e t
sub env (V v) = subVar env v
sub env (App x y) = App (sub env x) (sub env y)
sub env (Abs e) = Abs(sub (None env) e)
sub env (Pair x y) = Pair (sub env x) (sub env y)
sub env (Lit n) = Lit n
sub env (Pi1 x) = Pi1 (sub env x)
sub env (Pi2 x) = Pi2 (sub env x)

 
s1 = One (Lit 5) (None (One (Lit 6) Id))
 
------------------------------------------------------------
-- defining your own kinds

kind Natural = Zero | Succ Natural

data List n a 
  = Nil where n = Zero
  | forall m . Cons a (List m a) where n = Succ m

kind RowS = Rnil | Rcons *0 RowS

data Tuple r = Tnil where r = Rnil
             | forall t r' . Tcons t (Tuple r') where r = Rcons t r'

-------------------------------------------------------------
-- Polymorphic kinds

TRep :: forall (k :: *1 ) . (k ~> *0)
data TRep t
  = Int  where t = Int
  | Char where t = Char
  | Unit where t = ()
  | Prod where t = (,)
  | Sum  where t = (+)
  | Arr  where t = (->) 
  | ex (k1 :: *1) (f :: k1 ~> k) (x :: k1) .
          Ap (TRep f) (TRep x) where t = f x  
    
f :: forall (k :: *1) (t :: k) . TRep t -> Int
f Int = 1
f Prod = 2
f (Ap a b) = f a + f b

-----------------------------------------------------------
-- Tags and labels are predefined
-- kind Tag = %name | %age | ... | for all legal symbols
-- data Label t = %name where t=%name | %age where t = %age | ...

tim :: Label `tim
tim = `tim

------------------------------------------------------------
-- HasType and Rows are predefined


-- kind HasType = Has Tag *0
-- Row :: *1 ~> *1
-- kind Row x = RCons x (Row x) | RNil

data Variable :: Row HasType ~> HasType ~> *0 where
  V0 :: Variable (RCons (Has s t) env) (Has s t)
  Vn :: Variable env t -> Variable (RCons s env) t

data RowExp :: Row HasType ~> *0 ~> *0 where
  IntExp :: Int -> RowExp e Int
  Variable :: Label s -> (Variable env (Has s t)) -> RowExp env t

--------------------------------------------------------------------
-- Anonymous existential types

existsA :: exists t . (t,t->String)
existsA = Ex (5,\ x -> show(x+1))

testf :: (exists t . (t,t-> String)) -> String
testf (Ex (a,f)) = f a

------------------------------------------------------------
-- Duplicate variables in ranges

kind Ctype = Comb | Seq (*0 ~> *0)

data Var2 :: Row HasType ~> HasType ~> *0 where
  Vz :: Var2 (RCons (Has s t) env) (Has s t)
  Vm :: Var2 env t -> Var2 (RCons s env) t

data Exp2 :: Ctype ~> Row HasType ~> *0 ~> *0 where
  Var :: Label s -> Var2 env (Has s t) -> Exp2 c env t
  
data Decs2 :: Ctype ~> Row HasType ~> Row HasType ~> *0 ~> *0 where
   In :: (Exp2 c all t) -> Decs2 c all all t
--                                 ^   ^  Note duplicates!!!
-- this causes us to miss some equations.
 
----------------------------------------------
-- Type synonyms with arguments

type Pair x y = (x,y)

testg :: String -> Int -> Pair String Int
testg x y = (x,y)

----------------------------------------------
-- Qualified arguments with constraints

f7 :: (forall a . (a=Int) => (a,a)) -> Int
f7 (x,y) = x +y

try1 = f7 (2,3)

g7 :: (forall a . (a=b) => (a,b)) -> [b]
g7 (x,y) = [x,y]

try2 = g7(True,False)

----------------------------------------------------
-- Static constraints and propositions

prop LE :: Nat ~> Nat ~> *0 where
  Base:: LE Z a
  Step:: LE a b -> LE (S a) (S b)

data LE' x y = LE where LE x y

data SSeq a = Snil where a = Z
         | exists b . Scons (Nat' a) (SSeq b) where LE b a

##test "Refute (LE #3 #1)"
  bad23 = Scons #1 (Scons #3 Snil)
  
trans :: LE a b -> LE b c -> LE a c
trans Base Base = Base
-- trans (Step z) Base = UNREACHABLE CODE
trans Base (Step z) = Base
trans (Step x) (Step y) = (Step(trans x y))

compare :: Nat' a -> Nat' b -> (LE' a b + LE' b a)
compare Z Z     = L LE
compare (a@Z) (b@(S x)) = 
   case compare Z x of  
      L LE -> L LE
      R LE -> L LE
compare (a@(S x)) (b@Z) = 
   case compare x Z of  
      R LE -> R LE
      L LE -> R LE
compare (S x) (S y) =  
   case compare x y of  
      R LE -> R LE
      L LE -> L LE  
