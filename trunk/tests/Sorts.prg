-- Copyright (c) 2006 Portland State University.
-- This is an example program for the Omega programming language;
-- for more information, see:
--   http://www.cs.pdx.edu/~sheard/Omega/index.html
-- Research and development on Omega is supported by a grant
-- from the National Science Foundation.

-- Existential hiding and operators on anonymous sums

import "Covert.prg" (Covert,Hide,toNat)
import "Library.prg" (mapP,unP,map)
import "Nat.prg" (LE,Base_LE,Step_LE, compareN, magnitude, eqOrNe)

-------------------------------------------------
-- Sorted Sequence data

data SSeq :: Nat ~> *0 where
  Snil :: SSeq Z
  Scons :: Nat' n -> LE m n -> SSeq m -> SSeq n

--------------------------------------------------
-- insertion sort

--less a b = case compareN a b of {L x -> x; R y -> error "Not less"}
        
insert :: Nat' a -> SSeq b -> ((SSeq a)+(SSeq b))
insert z Snil = L(Scons z (magnitude z) Snil)
insert x (xs@(Scons y p zs)) = 
   case compareN x y of
     R q -> L(Scons x q xs)
     L q -> case insert x zs of
              L (mm) -> R(Scons y q mm)
              R (mm) -> R(Scons y p mm)

sort :: [Covert Nat'] -> Covert SSeq
sort [] = Hide Snil
sort ((Hide x):xs) = 
     case insert x ys of {L w -> Hide w; R w -> Hide w}
   where (Hide ys) = sort xs
          
--test :: Nat' x -> Nat' y -> ((Equal x y) + ())
--test Z Z = L Eq
--test (S x) (S y) = case (test x y) of { L Eq -> L Eq; R () -> ()}
--test _ _ = Nothing

test2 :: [Int] -> Covert SSeq
test2 xs = sort(map toNat xs)

x23 = test2 [0,3,1]

----------------------------------------------------
-- merge sort

merge :: SSeq n -> SSeq m -> (SSeq n + SSeq m)
merge Snil ys = R ys
merge xs Snil = L xs
merge (a@(Scons x px xs)) (b@(Scons y py ys)) =
  case compareN x y of
    L p -> case merge a ys of
             L ws -> R(Scons y p ws)
             R ws -> R(Scons y py ws)
    R p -> case merge b xs of
             L ws -> L(Scons x p ws)
             R ws -> L(Scons x px ws)

merge2 :: SSeq u -> SSeq v -> Covert SSeq
merge2 x y = unP (mapP Hide Hide (merge x y))

split [] pair = pair
split [x] (xs,ys) = (x:xs,ys)
split (x:y:zs) (xs,ys) = split zs (x:xs,y:ys)

msort :: [Covert Nat'] -> Covert SSeq
msort [] = Hide Snil
msort [Hide x] = Hide(Scons x (magnitude x) Snil)
msort xs = merge2 ys zs
  where (y,z) = split xs ([],[])
        (Hide ys) = msort y
        (Hide zs) = msort z

----------------------------------------------------
-- Bounded lists

data BSeq :: Nat ~> Nat ~> *0 where
  Nil :: LE min max => BSeq min max
  Cons :: (LE min m, LE m max) => Nat' m -> BSeq min max -> BSeq min max

qsplit :: (LE min piv, LE piv max) => Nat' piv -> BSeq min max -> (BSeq min piv,BSeq piv max)
qsplit piv Nil = (Nil,Nil)
qsplit piv (Cons x xs) = 
    case compareN x piv of
      L p1 -> (Cons x small, large)
      R p1 -> (small, Cons x large)
  where (small,large) = qsplit piv xs
         
-----------------------------------------------------         
data MaxAns :: *0 where
  MaxAns :: BSeq min max -> MaxAns

minmax (min,max) [] = (min,max)
minmax (min,max) (x:xs) = minmax (small min x,large max x) xs
  where small x y = if x < y then x else y
        large x y = if x > y then x else y

small :: Nat' x -> Nat' y -> LE x y
small x y = 
  case compareN x y of 
    L p -> p 
    R p -> error ("not smaller: "++show x++" "++show y)

initMaxAns :: [Int] -> MaxAns        
initMaxAns (ys@(x:xs)) =  MaxAns (case small minNat maxNat of
                             proof -> (f minNat maxNat ys))
 where (min,max) = minmax (x,x) xs
       (Hide minNat) = toNat min
       (Hide maxNat) = toNat max
       f :: (LE min max) => Nat' min -> Nat' max -> [Int] -> BSeq min max
       f min max [] = Nil
       f min max (n:ns) = case (small min nNat, small nNat max) of
                           (p,q) -> Cons nNat tail
         where tail = f min max ns
               (Hide nNat) = toNat n

  
------------------------------------------------------
-- Sorted lists

data SL :: Nat ~> Nat ~> *0 where
  SNil :: SL x x
  SCons :: LE min min' => Nat' min -> SL min' max -> SL min max

app :: SL min piv -> SL piv max -> SL min max
app SNil ys = ys
app (SCons min xs) ys = SCons min (app xs ys)

qsort1 :: BSeq min max -> exists t . LE min t => SL t max
qsort1 Nil = Ex(SNil)
qsort1 (Cons pivot tail) = Ex(app smaller' (SCons pivot larger'))
  where (smaller,larger) = qsplit pivot tail
        (Ex smaller') = (qsort1 smaller)
        (Ex larger') = (qsort1 larger)

 
--------------------------------------------------------------------
-- quick sort

data Sorted :: *0 where
  Sorted :: SL min max -> Sorted

qsort :: [Int] -> Sorted
qsort xs = Sorted list
   where (MaxAns ys) = initMaxAns xs
         (Ex list) = qsort1 ys
