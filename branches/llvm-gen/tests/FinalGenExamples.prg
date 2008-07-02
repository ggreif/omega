{- Predefined
data Nat :: *1 where
  Z :: Nat
  S :: Nat ~> Nat
-}

plus:: Nat ~> Nat ~> Nat
{plus Z m} = m
{plus (S n) m} = S {plus n m}

data Seq:: *0 ~> Nat ~> *0 where
  Snil :: Seq a Z
  Scons:: a -> Seq a n -> Seq a (S n)
  
l1 = (Scons 3 (Scons 5 Snil)) :: Seq Int (S(S Z))

app:: Seq a n -> Seq a m -> Seq a {plus n m}
app Snil ys = ys
app (Scons x xs) ys = Scons x (app xs ys)  

----------------------------------------

data Boolean:: *1 where
  T:: Boolean
  F:: Boolean
  
kind TempUnit:: *1 where
   Fahrenheit:: TempUnit
   Celsius:: TempUnit
   Kelvin:: TempUnit  
   
data Degree:: TempUnit ~> *0 where
  F :: Float -> Degree Fahrenheit
  C :: Float -> Degree Celsius
  K :: Float -> Degree Kelvin   
  
add :: Degree a -> Degree a -> Degree a
add (F n) (F m) = F(n #+ n)
add (C n) (C m) = C(n #+ n)
add (K n) (K m) = K(n #+ n)    

plusK :: Degree a -> Degree b -> Degree Kelvin
plusK (K x) (K y) = K(x #+ y)
plusK (C x) (K y) = K(273.0 #+ x #+ y) 

------------------------------------------
le:: Nat ~> Nat ~> Boolean 
{le Z n} = T
{le (S n) Z} = F
{le (S n) (S m)} = {le n m}

and:: Boolean ~> Boolean ~> Boolean
{and T x} = x
{and F x} = F

even :: Nat ~> Boolean
{even Z} = T
{even (S Z)} = F
{even (S (S n))} = {even n}

-----------------------------------

data Even:: Nat ~> *0 where
  EvenZ:: Even Z
  EvenSS:: Even n -> Even (S (S n))
  
data LE:: Nat ~> Nat ~> *0 where
  LeZ:: LE Z n
  LeS:: LE n m -> LE (S n) (S m)
  
_ = EvenZ:: Even #0
_ = (EvenSS EvenZ):: Even #2
_ = (EvenSS (EvenSS EvenZ)):: Even #4  

data Sum:: Nat ~> Nat ~> Nat ~> *0 where
  PlusZ:: Sum Z m m
  PlusS:: Sum n m z -> Sum (S n) m (S z)

p1 ::Sum #2 #3 #5
p1 = PlusS (PlusS PlusZ)
------------------------------------------
data Tree a = Fork (Tree a) (Tree a) | Node a | Tip

---------------------------------------

data SNat:: Nat ~> *0 where
  ZerO:: SNat Z
  SucC:: SNat n -> SNat (S n)
  
three = (SucC (SucC (SucC ZerO))):: SNat(S(S(S Z)))

-------------------------------------------
{- Predefined
data Nat':: Nat ~> *0 where
  Z:: Nat' Z
  S:: Nat' n -> Nat' (S n)
-}

three' = (S(S(S Z))):: Nat'(S(S(S Z)))

--------------------------------------
app1:: Seq a n -> Seq a m -> exists p . (Seq a p,Sum n m p)
app1 Snil ys = Ex(ys,PlusZ)
app1 (Scons x xs) ys = case (app1 xs ys) of { Ex(zs,p) ->  Ex(Scons x zs,PlusS p) }


---------------------------------------
inc x = x + 1
c1a = [| 4 + 3 |]
c2a = [| \ x -> x + $c1a |]
c3 = [| let f x = y - 1 where y = 3 * x in f 4 + 3 |]
c4 = [| inc 3 |]

c5 = [| [| 3 |] |]
c6 = [| \ x -> x |]


-------------------------------------
data Rep:: *0 ~> *0 where
  Rint:: Rep Int  
  Rchar:: Rep Char 
  Runit:: Rep ()
  Rpair:: Rep a -> Rep b -> Rep (a,b)
  Rsum::  Rep a -> Rep b -> Rep (a+b) -- In Omega, (a+b) is like (Either a b) in Haskell

t1 :: Rep ((Int,Char)+((),Int))  
t1 = Rsum(Rpair Rint Rchar) (Rpair Runit Rint) 

sumR :: Rep a -> a -> Int
sumR Rint n = n
sumR (Rpair r s) (x,y) = sumR r x + sumR s y
sumR (Rsum r s) (L x) = sumR r x     -- L:: a -> (a+b) is a sum injection function
sumR (Rsum r s) (R x) = sumR s x     -- R:: b -> (a+b)
sumR _ x = 0  

fst(x,y) = x
snd (x,y) = y

sum2 :: Rep a -> Code a -> Code Int
sum2 Rint x = x
sum2 (Rpair x y) z = 
  [| let (a,b) = $z in $(sum2 x [| a |]) + $(sum2 y [| b |]) |]
sum2 (Rsum r s) x = 
  [| case $x of
       L m -> $(sum2 r [| m |])
       R m -> $(sum2 s [| m |]) |]
sum2 _ x = [| 0 |]                         

sumG x = [| \ w -> $(sum2 x [| w |]) |]

ans3 = sumG t1

-----------------------------------

sumTy :: Nat ~> *0
{sumTy Z} = Int
{sumTy (S n)} = Int -> {sumTy n}

nsumAcc :: Nat' n -> Int -> {sumTy n}
nsumAcc Z x = x
nsumAcc (S n) x = \ y -> (nsumAcc n (x+y))

nsum :: Nat' n -> {sumTy n}
nsum n = nsumAcc n 0

testsum = (nsum #3 1 3 5) == (nsum #2 0 9) 

nsumG :: Nat' n -> Code Int -> Code {sumTy n}
nsumG Z x = x 
nsumG (S n) x = [| \ y -> $(nsumG n [| $x + y |]) |]

sumGen:: Nat' n -> Code {sumTy n}
sumGen n = nsumG n (lift 0)

ans4 = sumGen (S(S(S Z)))
-------------------------------------------------

data MapSpec :: Nat ~> *0 ~> *0 ~> *0 ~> *0 where
  One:: MapSpec (S Z) (a -> b) [a] [b]
  Suc:: MapSpec m x y z -> MapSpec (S m) (a -> x) [a] (y -> z)
  
  
  
one = One:: MapSpec #1 (a -> b) [a] [b]
two = (Suc One):: MapSpec #2 (a -> b -> c) [a] ([b] -> [c])
thre = (Suc (Suc One)):: MapSpec #3 (a -> b -> c -> d) [a] ([b] -> [c] -> [d])
four = (Suc (Suc (Suc One))):: MapSpec #4 (a -> b -> c -> d -> e) [a] ([b] -> [c] -> [d] -> [e])   


mapflat:: MapSpec n a b c -> a -> (b -> c) -> b -> c
mapflat One f recall (x:xs) = f x : recall xs
mapflat One f recall [] = []
mapflat (Suc n) f recall (x:xs) = mapflat n (f x) (recall xs)
mapflat (Suc n) f recall [] = default (Suc n)

default:: MapSpec n a b c -> c
default One = []
default (Suc n) = \ _ -> default n 

map:: MapSpec n a b c -> a -> b -> c
map n f x = mapflat n f (map n f) x

mapGen:: MapSpec n a b c -> Code a -> Code(b -> c) -> Code(b -> c)
mapGen One f recall = 
  [| \ ys -> case ys of
       (x:xs) -> $f x : $recall xs 
       [] -> $(lift []) |]  
mapGen (Suc n) f recall = 
  [| \ ys -> 
       case ys of 
         (x:xs) -> $(mapGen n [| $f x |] [| $recall xs |]) 
         [] -> $(defaultCode (Suc n)) |] 
         
defaultCode:: MapSpec n a b c -> Code c
defaultCode One = lift [] 
defaultCode (Suc n) = [| \ _ -> $(defaultCode n) |]  

mapCode:: MapSpec n a b c -> Code( a -> b -> c )
mapCode n = 
  [| let map f = $(mapGen n [|f|] [| map f |])
     in map
  |]
  
------------------------------------------ 
sumList [] = 0
sumList (x:xs) = x + sumList xs

mapList f [] = []
mapList f (x:xs) = f x : mapList f xs


data TypeS:: *0 ~> *0  where
  Charx:: TypeS Char
  Intx:: TypeS Int
  AppS_S:: TypeS_S phi -> TypeS a -> TypeS (phi a)

data TypeS_S:: (*0 ~> *0) ~> *0  where
  Listx:: TypeS_S []
  Treex:: TypeS_S Tree
  AppSS_S:: TypeS_S_S phi -> TypeS a -> TypeS_S (phi a)
  
data TypeS_S_S:: (*0 ~> *0 ~> *0) ~> *0  where
  Pairx:: TypeS_S_S (,)
  
  
data Type:: forall (k:: *2) (t::k) . k ~> t ~> *0  where
  Char:: Type *0 Char
  Int:: Type *0 Int
  App:: forall (i:: *1) (j:: *1) (f:: i~>j) (x:: i) .
        Type (i ~> j) f -> Type i x -> Type j (f x)
  List:: Type (*0 ~> *0) []
  Tree:: Type (*0 ~> *0) Tree
  Pair:: Type (*0 ~> *0 ~> *0) (,)   
  
------------------------------
countTy:: forall (k:: *2) (t::k) . k ~> t ~> *0
{countTy *0 a} = a -> Int
{countTy (i ~> k) phi} = {countTy i a} -> {countTy k (phi a)}

countTyInjective1:: Kind' a -> Equal {countTy a x} {countTy a y} -> Equal x y
countTyInjective1 Star Eq = Eq
countTyInjective1 (Karr x y) Eq = Eq
  where theorem ih1 = countTyInjective1 x,
                ih2 = countTyInjective1 y

prop Kind':: *1 ~> *0 where
  Star :: Kind' *0
  Karr :: Kind' a -> Kind' b -> Kind' (a ~> b)

-------------------------------
 
const n x = n

count::  forall (k:: *1) (t::k) . Type k t -> {countTy k t}
count Char = const 0
count Int = const 0
count (App f a) = (count f) (count a)     where theorem countTyInjective1
count List = \ c -> sumList . mapList c
count Tree = \ c -> sumTree . mapTree c 
count Pair = \ c1 c2 (x,y) -> c1 x + c2 y 

size:: forall (f:: *0 ~> *0) (a:: *0) . Type (*0 ~> *0) f -> f a -> Int
size f = count f (const 1)

sum:: Type (*0 ~> *0) f -> f Int -> Int
sum f = count f (\ x -> x)

-----------------------------------------

sumTree (Tip) = 0
sumTree (Node a) = a
sumTree (Fork x y) = sumTree x + sumTree y

mapTree f (Tip) = Tip
mapTree f (Node a) = Node(f a)
mapTree f (Fork x y) = Fork (mapTree f x) (mapTree f y)

--------------------------------------------------

-- Fridlender and Indrika: Do We Need Dependent Types

lap (f:fs) (x:xs) = (f x) : (lap fs xs)
lap _ _ = []


repeat x = x : (lazy (repeat x))
map3 f xs ys zs = repeat f `lap` xs `lap` ys `lap` zs

-- prompt> map3 (\ x y z -> (x,y,z)) [1,2,3] [True,False] "abcde"
-- [(1,(True,'a')),(2,(False,'b'))] : [(Int,(Bool,Char))]

zero:: a -> a
zero x = x

succ:: ([a] -> b) -> [c -> a] -> [c] -> b
succ n fs xs = n(fs `lap` xs)

zip:: ([a] -> b) -> a -> b
zip n f = n (repeat f)

ex34 = zip (succ (succ (succ zero))) 
           (\ x y z -> (x,y,z)) 
           [1,2,3] [True,False] "abcde"
            
           
succS n fs = [| \ xs -> $(n [|lap $fs xs|]) |]
zeroS x = x
mapS n = [| \ f -> $(n [|repeat f|]) |]

---------------------------------------------------
data Zip:: *0 ~> *0 ~> *0 where
  Zero :: Zip [a] [a]
  Succ :: Zip [x] y -> Zip [a -> x] ([a] -> y)
  
zip2 :: Zip [x] y -> x -> y
zip2 n f = zip' n (repeat f)
  where zip' :: Zip x y -> x -> y
        zip' Zero xs = xs
        zip' (Succ n) fs = \ xs -> zip' n (apply fs xs)

zipGen :: Zip [x] y -> Code(x -> y)
zipGen n = [| \ f -> $(zip' n [| repeat f |]) |]
  where zip' :: Zip x y -> Code x -> Code y
        zip' Zero xs = xs
        zip' (Succ n) fs = [| \ xs -> $(zip' n [| apply $fs xs |] ) |]

zero_ :: Zip [a] [a]
zero_ = Zero

one_ :: Zip [a -> b] ([a] -> [b])
one_ = Succ Zero

two_ :: Zip [a -> b -> c] ([a] -> [b] -> [c])
two_ = Succ(Succ Zero)

test = zipGen (Succ (Succ Zero))
-- prompt> zipGen (Succ (Succ Zero))
-- [| \ f -> \ xs -> \ ys -> %apply (%apply (%repeat f) xs) ys |] 

data Zip' :: *0 ~> *0 ~> *0 where
  Zero':: Zip' a [a]
  Succ':: Zip' b c -> Zip' (a -> b) ([a] -> c)

zero' :: Zip' a [a]
zero' = Zero'

one' :: Zip' (a -> b) ([a] -> [b])
one' = Succ' Zero'

two':: Zip' (a -> b -> c) ([a] -> [b] -> [c])
two' = Succ' (Succ' Zero')


zip_ n = let map f =  zip' n f (\ x -> map f x) in map 
 where default:: Zip' a b -> b
       default Zero' = []
       default (Succ' n) = \ ys -> default n
       
       zip' :: Zip' a b -> a -> b -> b
       zip' Zero' x xs = (x : xs)
       zip' (Succ' n) f rcall = 
          (\ ys -> case ys of
               (z:zs) -> zip' n (f z) (rcall zs)
               _ -> default n)


add1 x = x+1
ff = zip_ (Succ' Zero')

                   
zipGen_ n = [| let map f =  $(zip' n [|f|] [|map f|]) in map |]
 where default:: Zip' a b -> Code b
       default Zero' = [| [] |]
       default (Succ' n) = [| \ ys -> $(default n) |] 
       
       zip' :: Zip' a b -> Code a -> Code b -> Code b
       zip' Zero' x xs = [| $x : $xs |]
       zip' (Succ' n) f rcall = 
          [| \ ys -> case ys of
              (z:zs) -> $(zip' n [| $f z |] [| $rcall zs |])
              _ -> $(default n) |]  

test' = zipGen_ (Succ'(Succ' Zero'))                    
 
------------------------------------------- 
{-
repeat :: a -> [a]
repeat a = a : (lazy (repeat a))

map f [] = []
map f (x:xs) = f x : map f xs
-}

apply:: [a -> b] -> [a] -> [b]
apply (f:fs) (x :xs) = f x : apply fs xs
apply _ _ = []
