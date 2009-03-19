kind Color  = Red | Black
kind State = Locked | Unlocked | Error

-- kind Nat = Z | Succ Nat

kind Degree = Kelvin | Fahrenheit | Celsius

data Even :: Nat ~> *0  where
  EvenZ:: Even Z
  EvenS:: Odd n -> Even (S n)
  
data Odd :: Nat ~> *0  where
  OddS:: Even n -> Odd(S n)

prop LE :: Nat ~> Nat ~> *0  where
  Base:: LE Z x
  Step:: LE x y -> LE (S x) (S y) 

even2 :: Even #2
even2 = EvenS(OddS EvenZ)

odd1 :: Odd #1
odd1 = OddS EvenZ

le23 :: LE #2 #3
le23 = Step(Step Base)

le2x :: LE #2 (S(S a))
le2x = Step(Step Base)

------------------------------------------
-- Singleton types

s2:: Nat' #2
s2 = S (S Z) 

-------------------------------------------
-- Merge sort

-- DynamicSortedSequence
data Dss:: Nat ~> *0 where
  Dnil:: Dss Z 
  Dcons:: (Nat' n) -> (LE m n) -> (Dss m) -> Dss n

comp :: Nat' a -> Nat' b -> (LE a b + LE b a)
comp Z Z     = L Base
comp (a@Z) (b@(S x)) = L Base
comp (a@(S x)) (b@Z) = R Base
comp (S x) (S y) =  
   case comp x y of  
      R p -> R (Step p)
      L p -> L (Step p)

merge :: Dss n -> Dss m -> (Dss n + Dss m)
merge Dnil ys = R ys
merge xs Dnil = L xs
merge (a@(Dcons x px xs)) (b@(Dcons y py ys)) =
  case comp x y of
    L p -> case merge a ys of
             L ws -> R(Dcons y p ws)
             R ws -> R(Dcons y py ws)
    R p -> case merge b xs of
             L ws -> L(Dcons x p ws)
             R ws -> L(Dcons x px ws)

data Covert:: (Nat ~> *0) ~> *0 where
   Hide::  (t x) -> Covert t

inputList :: [Covert Nat']
inputList = [Hide #1,Hide #2,Hide #4, Hide #3]

split [] pair = pair
split [x] (xs,ys) = (x:xs,ys)
split (x:y:zs) (xs,ys) = split zs (x:xs,y:ys)

msort :: [Covert Nat'] -> Covert Dss
msort [] = Hide Dnil
msort [Hide x] = Hide(Dcons x Base Dnil)
msort xs = 
  let (y,z) = split xs ([],[])
      (Hide ys) = msort y
      (Hide zs) = msort z
  in case merge ys zs of
      L z -> Hide z
      R z -> Hide z
  
ans = msort inputList

------------------------------------------------------------
trans :: LE a b -> LE b c -> LE a c
trans Base Base = Base
trans (Step z) Base = unreachable
trans Base (Step z) = Base
trans (Step x) (Step y) = (Step(trans x y))

 
--f :: forall a b c . (LE c b,LE b a) => Nat' a -> Nat' b -> Sss c -> Sss a
--f x y z = Scons x (Scons y z)

-----------------------------------------------
-- Static versions

-- StaticSortedSequence
{-
data Sss t 
  = Snil where t = Z
  | exists m . Scons (Nat' t) (Sss m) where LE m t
-}

data Sss:: Nat ~> *0 where
  Snil :: Sss Z
  Scons :: LE m t => Nat' t -> Sss m -> Sss t

data LE' :: Nat ~> Nat ~> *0 where
   LE :: LE m n => LE' m n
   
compare :: Nat' a -> Nat' b -> (LE' a b + LE' b a)
compare Z Z     = L LE
compare Z (S x) = L LE
compare (S x) Z =  R LE
compare (a@(S x)) (b@(S y)) =  
   case compare x y of  
      R (p@LE) -> (R LE)
      L LE -> (L LE)
{-
compare Z (S x) = 
   case compare Z x of  
      L LE -> L LE
      R LE -> L LE
compare (S x) Z = 
   case compare x Z of  
      R LE -> R LE
      L LE -> R LE
-}


merge2 :: Sss n -> Sss m -> (Sss n + Sss m)
merge2 Snil ys = R ys
merge2 xs Snil = L xs
merge2 (a@(Scons x xs)) (b@(Scons y ys)) =
  case compare x y of
    L LE -> case merge2 a ys of
             L ws -> R(Scons y ws)           
             R ws -> R(Scons y ws)
    R LE -> case merge2 b xs of
             L ws -> L(Scons x ws)
             R ws -> L(Scons x ws)

msort2 :: [Covert Nat'] -> Covert Sss
msort2 [] = Hide Snil
msort2 [Hide x] = Hide(Scons x Snil)
msort2 xs = 
  let (y,z) = split xs ([],[])
      (Hide ys) = msort2 y
      (Hide zs) = msort2 z
  in case merge2 ys zs of
      L z -> Hide z
      R z -> Hide z

ans2 = msort2 inputList
-- (Hide (Scons #4 (Scons #3 (Scons #2 (Scons #1 Snil))))) : Covert Sss

---------------------------------------------------
data RowT :: *1 ~> *1 where
   RConsX :: x ~> (RowT x) ~> RowT x
   RNilX :: RowT x
 
data Tuple:: RowT *0 ~> *0 where
  Tnil:: Tuple RNilX
  Tcons:: t -> Tuple r -> Tuple (RConsX t r)
               
t1 = Tcons 5 (Tcons True Tnil)
-- (Tcons 5 (Tcons True Tnil)) : Tuple {Int,Bool}

data List:: Nat ~> *0 ~> *0 where
  Nil:: List Z a
  Cons::  a -> List m a -> List (S m) a

data Term :: *0 ~> *0 where
  Const :: a -> Term a
  Pair :: Term a -> Term b -> Term (a,b)
  App :: Term(a -> b) -> Term a -> Term b

------------------------------------------------------

data Mod :: Nat ~> *0 where
  Mod :: Int -> Nat' n -> Mod n

x:: Mod #3
x = Mod 6 #3 

y:: Mod #2
y = Mod 6 #2

-- A conversion function
natToInt :: Nat' n -> Int
natToInt Z = 0
natToInt (S n) = 1 + natToInt n

normalize :: Mod n -> Mod n
normalize (Mod val n) = Mod (mod val (natToInt n)) n

plusM :: Mod n -> Mod n -> Mod n
plusM (Mod a n) (Mod b _) = normalize (Mod (a+b) n)

minusM :: Mod n -> Mod n -> Mod n
minusM (Mod a n) (Mod b _) = normalize (Mod (a-b) n)

timesM :: Mod n -> Mod n -> Mod n
timesM (Mod a n) (Mod b _) = normalize (Mod (a*b) n)



--------------------------------------------------
-- Primes:
prop Prime :: Nat ~> *0 where
  Two   :: Prime #2
  Three :: Prime #3
  Five  :: Prime #5
  Seven :: Prime #7
  -- I don't know how to generalize

invM :: forall n . (Prime n) => Mod n -> Mod n
invM (Mod a n) = Mod (mod b n') n
  where n' = natToInt n
        (_,_,b) = gcd n' a

gcd p q | q > p = gcd q p
gcd p q | q==0 = (p,1,0)
gcd p q = (g,y1,x1 - (p `div` q)*y1)
  where (g,x1,y1) = gcd q (p `mod` q)
