
plus :: Nat ~> Nat ~> Nat
{plus Z n} = n
{plus (S x) n} = S {plus x n}

pow2 :: Nat ~> Nat
{pow2 Z} = S Z
{pow2 (S x)} = {plus {pow2 x} {pow2 x}}

half :: Nat ~> Nat
{half Z} = Z
{half (S Z)} = Z
{half (S (S n))} = S {half n}

log :: Nat ~> Nat
{log Z} = S Z
{log (S Z)} = S Z
{log (S (S n))} = S {log (S {half n})}

-------------------------------------------------
-- Theorems about Natural numbers and plus

plusZ :: Nat' n -> Equal {plus n Z} n
plusZ Z = Eq
plusZ (x@(S m)) = Eq
  where theorem indHyp = plusZ m
  
plusS :: Nat' n -> Equal {plus n (S m)} (S{plus n m})
plusS Z  = Eq
plusS (S x)  = Eq
  where theorem ih = plusS x

plusAssoc :: Nat' n -> Equal {plus {plus n b} c} {plus n {plus b c}}
plusAssoc Z = Eq
plusAssoc (S n) = Eq
  where theorem ih = plusAssoc n

plusCommutes :: Nat' n -> Nat' m -> Equal {plus n m} {plus m n}
plusCommutes Z m = Eq
   where theorem lemma = plusZ m
plusCommutes (S x) m = Eq
   where theorem plusS,
                 indHyp = plusCommutes x m

plusNorm :: Nat' x -> Equal {plus x {plus y z}} {plus y {plus x z}}
plusNorm Z = Eq
plusNorm (S n) = Eq
  where theorem plusS, ih = plusNorm n

lemma2:: Nat' n -> Equal {plus n n} (S(S m)) -> 
         exists j . (Equal n (S j),Equal m {plus j j})
lemma2 Z Eq = unreachable         
lemma2 (S n) (p@Eq) = Ex (Eq,Eq)
   where theorem plusS

ppZ:: Nat' n -> Equal {plus n m} Z -> (Equal n Z,Equal m Z)
ppZ (x@Z) (y@Eq) = (Eq,Eq)
ppZ (S n) Eq = unreachable

------------------------------------------------
-- theorems about pow2

notZpow2 :: Nat' n -> exists m . Equal {pow2 n} (S m)
notZpow2 Z = Ex Eq
notZpow2 (S n) = (Ex Eq)
 where theorem indHyp = (notZpow2 n)

------------------------------------------------
-- operations on Nat'

halve:: Nat' {plus n n} -> Nat' n
halve Z = Z
  where theorem ppZ
halve (S Z) = unreachable  
halve (x@(S (S n))) = (S (halve n))
  where theorem plusS,lemma2

-- We first tried to give halve the type of halveP, but this
-- type is too strong to make a recursive call. By defining
-- it with the weaker type, we succeed, and then we can easily
-- specialize this weaker type!!!!

halveP :: Nat' {pow2 (S n)} -> Nat' {pow2 n}
halveP = halve

add:: Nat' n -> Nat' m -> Nat' {plus n m}
add Z n = n
add (S m) n = S(add m n)

divBy2:: Nat' n -> exists r d . (Nat' d,Bit r,Equal n {plus r {plus d d}})
divBy2 Z = Ex(Z,Zero,Eq)
divBy2 (S Z) = Ex(Z,Uno,Eq)
divBy2 (w@(S (S n))) = 
   case divBy2 n of 
     (Ex(m,r,p@Eq)) -> Ex(S m,r,Eq)
        where theorem plusS                    

-----------------------------------------------------------

data OneHi:: Nat ~> Nat ~> *0 where
  One:: Nat' n -> OneHi n (S n)
  Pad:: OneHi value width -> OneHi value (S width)

data Bus :: Nat ~> Nat ~> *0 where
 Nil:: Bus Z Z
 O:: Bus value width -> Bus value (S width)
 I:: Bus value width -> Bus {plus value {pow2 width}} (S width)

data Bit:: Nat ~> *0 where
  Zero:: Bit Z
  Uno:: Bit (S Z)

-------------------------------------
-- examples

ex0 = One #4  -- 10000

ex1 :: OneHi #2 #5  
ex1 = Pad (Pad (One #2)) --  00100 

ex2 = Pad (One #0) -- 01


ex3:: Bus #5 #3
ex3 = I(O(I Nil))

----------------------------------

width:: Bus v w -> Nat' {pow2 w}
width Nil = S Z
width (O xs) = let n = (width xs) in add n n
width (I xs) = let n = (width xs) in add n n

padLeft:: Nat' n -> OneHi v w -> OneHi v {plus n w}
padLeft Z x = x
padLeft (S n) x = Pad (padLeft n x)

-- Note that the order {plus v w} vs {plus w v} matters
padR:: Nat' n -> OneHi v w -> OneHi {plus v n} {plus w n}
padR n (One m) = One (add m n) 
padR n (Pad xs) = Pad (padR n xs)

deMux:: Bus value width -> OneHi value {pow2 width} 
deMux Nil = One Z
deMux (O xs) = padLeft (width xs) (deMux xs)
deMux (I xs) = padR (width xs) (deMux xs)

--------------------------------------------------

push:: Bit i -> Bus n w -> Bus {plus i {plus n n}} (S w)
push Zero Nil = O Nil
push Uno Nil = I Nil
push x (O n) = O(push x n)
push x (I n) = I(push x n)
   where theorem plusAssoc, plusCommutes   

convert:: Nat' n -> exists w . Bus n w
convert Z = Ex (O Nil)
convert (S Z) = Ex(I Nil)
convert (n@(S (S _))) = 
  case divBy2 n of
    Ex(m,bit,p@Eq) -> 
      case convert m of
        Ex bus -> Ex (push bit bus)


halfDouble :: Nat' n -> Equal {half {plus n n}} n
halfDouble Z = Eq
halfDouble (S n) = Eq
  where theorem ih = halfDouble n, plusS

th:: Nat' b -> Equal (S(S a)) {plus b b} -> Equal (S{half a}) b
th Z Eq = unreachable
th (S n) (p@Eq) = Eq
  where theorem ih = halfDouble, plusS

th2 :: Nat' c -> Equal (S a) {plus c c} -> Equal (S {half a}) c
th2 Z Eq = unreachable
th2 (S n) (p@Eq) = Eq
   where theorem plusS,halfSDouble
   
halfSDouble :: Nat' n -> Equal {half (S{plus n n})} n
halfSDouble Z = Eq
halfSDouble (S n) = Eq
  where theorem ih = halfSDouble n, plusS  

conv:: Nat' n -> Bus n {log n}
conv Z =  (O Nil)
conv (S Z) = (I Nil)
conv (n@(S (S _))) = 
  case divBy2 n of
    Ex(m,Zero,p@Eq) -> (push Zero (conv m)) where theorem th
    Ex(m,Uno,p@Eq) -> push Uno (conv m) where theorem th2

--------------------------------------------------------

lemma :: Nat' x -> Equal {plus {pow2 x} {pow2 x}} #2 -> Equal x Z
lemma Z Eq = Eq
lemma (S n) Eq = unreachable
  where theorem notZpow2,plusS

chop :: OneHi v {pow2 (S n)} -> 
           ((exists m .(Equal v {plus m {pow2 n}},OneHi m {pow2 n}))
           +(OneHi n {pow2 n}))
chop (One Z) = unreachable  
  where theorem notZpow2, plusS
chop (One (S Z)) = L(Ex(Eq,One Z))
  where theorem lemma
--chop (One (S (S n))) =   

--------------------------------------------------------
lemma1 :: Equal (S a) w -> Equal (S {plus a b}) {plus w b}
lemma1 Eq = Eq

ff :: Equal i {plus a b} -> Equal {plus a {plus b c}} {plus i c}
ff Eq = Eq
  where theorem plusAssoc, plusCommutes, plusNorm 

incr:: Bus w v -> Bus (S w) (S v)
incr Nil = I Nil
incr (O n) = O(incr n)
incr (I n) = case (incr n) of
              (I m) -> (I(O m)) 
 where theorem plusAssoc,lemma1   -- or use lemma ff

bin:: Nat' n -> Bus v width -> Bus {plus n v} (S width)
bin n bus = 
  case divBy2 n of
    Ex(u@Z,v@Zero,p@Eq) -> O bus
--    Ex(u@Z,v@Uno,p@Eq) -> check I bus

binary:: Nat' n -> exists width . Bus n width
binary n = 
  case divBy2 n of
    Ex(Z,Zero,p@Eq) -> Ex Nil
    Ex(Z,Uno,p@Eq) -> Ex (I Nil) -- try Ex(O nil) to see what happens

