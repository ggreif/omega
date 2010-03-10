-- Discrete sets using type functions
-- Yay...

data Pair :: forall a b . a ~> b ~> *1 where
    P :: forall a b . a ~> b ~> Pair a b
  deriving Pair(q)

data Pair0 :: forall a b . Pair a b ~> *0 where
    P :: forall a b . a -> b -> Pair0 (P a b)
  deriving Pair(p)

data Cmp :: forall a b . a ~> b ~> *1 where
    G :: forall a b . a ~> b ~> Cmp a b
    L :: forall a b . a ~> b ~> Cmp a b
    E :: forall a b . a ~> b ~> Cmp a b
    N :: forall a b . a ~> b ~> Cmp a b -- No comparison possible

data Set1 :: *1 where
    Empty :: Set1
    U :: Nat ~> Set1 ~> Set1
 deriving List(set)

data Set0 :: Set1 ~> *0 where
    Empty :: Set0 Empty
    U :: Nat' n -> Set0 s -> Set0 {setInsert n s}
    Union :: Set0 s1 -> Set0 s2 -> Set0 {union s1 s2}
    Isect :: Set0 s1 -> Set0 s2 -> Set0 {intersect s1 s2}
    Diff :: Set0 s1 -> Set0 s2 -> Set0 {difference s1 s2}
    SymDiff :: Set0 s1 -> Set0 s2 -> Set0 {difference {union s1 s2} {intersect s1 s2}}

-- So this is sort of a strange beast
-- Compare the first elements of the pairs,
-- then return a tag telling which one was larger
-- along with the second elements of each pair...
-- i.e. cmp (a,x) (b,y)     -> L x y if (a < b)
--                          -> G x y if (a > b)
--                          -> E x y if (a = b)
cmp :: forall a b . Pair Nat a ~> Pair Nat b ~> Cmp a b
{cmp (P Z s1) (P Z s2)} = E s1 s2
{cmp (P Z s1) (P (S m) s2)} = L s1 s2
{cmp (P (S n) s1) (P Z s2)} = G s1 s2
{cmp (P (S n) s1) (P (S m) s2)} = {cmp (P n s1) (P m s2)}

-- Compare helper function for sets
setCmp :: Set1 ~> Set1 ~> Cmp Set1 Set1
{setCmp Empty Empty} = N Empty Empty
{setCmp (U n s) Empty} = N (U n s) Empty
{setCmp Empty (U m s)} = N Empty (U m s)
{setCmp (U n s1) (U m s2)} = {cmp (P n (U n s1)) (P m (U m s2))}

-- Compare helper function for insert and remove
natCmp :: Nat ~> Set1 ~> Cmp Nat Set1
{natCmp n Empty} = N n Empty
{natCmp n (U m s)} = {cmp (P n n) (P m (U m s))}

-- Maintain an ordered list
setInsert :: Nat ~> Set1 ~> Set1
{setInsert n s} = {setInsert' {natCmp n s}}

setInsert':: Cmp Nat Set1 ~> Set1
{setInsert' (N n Empty)} = U n Empty
{setInsert' (E n s)} = s
{setInsert' (L n (U m s))} = U m {setInsert' {natCmp n s}}
{setInsert' (G n s)} = U n s

-- Produce a set that does not contain
setRemove :: Nat ~> Set1 ~> Set1
{setRemove n s} = {setRemove' {natCmp n s}}

setRemove' :: Cmp Nat Set1 ~> Set1
{setRemove' (N n Empty)} = Empty
{setRemove' (E n (U n s))} = s -- remove n
{setRemove' (L n (U m s))} = U m {setRemove' {natCmp n s}}
{setRemove' (G n s)} = s

-- Definition of union', which uses this strange Cmp nonsense
union :: Set1 ~> Set1 ~> Set1
{union s1 s2} = {union' {setCmp s1 s2}}

union' :: Cmp Set1 Set1 ~> Set1
{union' (N Empty Empty)} = Empty
{union' (N (U n s1) Empty)} = (U n s1)
{union' (N Empty (U m s2))} = (U m s2)
{union' (E (U n s1) (U n s2))} = U n {union' {setCmp s1 s2}}
{union' (L (U n s1) (U m s2))} = U m {union' {setCmp (U n s1) s2}}
{union' (G (U n s1) (U m s2))} = U n {union' {setCmp s1 (U m s2)}}

-- Definition of intersect', which also uses Cmp
intersect :: Set1 ~> Set1 ~> Set1
{intersect s1 s2} = {intersect' {setCmp s1 s2}}

intersect' :: Cmp Set1 Set1 ~> Set1
{intersect' (N x y)} = Empty
{intersect' (L s1 (U m s2'))} = {intersect' {setCmp s1 s2'}}
{intersect' (G (U n s1') s2)} = {intersect' {setCmp s1' s2}}
{intersect' (E (U n s1') (U n s2'))} = U n {intersect' {setCmp s1' s2'}}

-- The difference' of sets... blah blah blah
difference :: Set1 ~> Set1 ~> Set1
{difference s1 s2} = {difference' {setCmp s1 s2}}

difference' :: Cmp Set1 Set1 ~> Set1
{difference' (N Empty Empty)} = Empty
{difference' (N (U n s1') Empty)} = U n s1'
{difference' (N Empty (U m s2'))} = Empty
{difference' (E (U n s1') (U n s2'))} = {difference' {setCmp s1' s2'}}
{difference' (L s1 (U m s2'))} = {difference' {setCmp s1 s2'}}
{difference' (G (U n s1') s2)} = U n {difference' {setCmp s1' s2}}
---
---

{-
ex1 = U #3 Empty
ex2 = U #3 (U #4 Empty)
ex3 = U #9 (U #10 (U #8 Empty))
ex4 = U #10 (U #11 Empty)
-}

-- Exceeds narrowing resources no matter
-- what the bounds?  Max Nat' is #19


ex4' = U #5 (U #3 (U #19 (U #19 (U #5 Empty))))

{-
ex5 = Union ex2 ex3
ex6 = Union ex1 ex5
ex7 = Union ex2 (Union ex1 (Union ex3 (Union ex5 (Union ex6 Empty))))

ex8 = Isect ex1 ex1
ex9 = Isect ex2 ex3
ex10 = Isect ex7 ex1

ex11 = Union (Isect ex1 ex2) (Isect ex3 ex4)

ex12 = Diff ex1 ex4

ex13 = SymDiff ex1 ex2
-}

data Witness :: Pair Set1 Set1 ~> Pair Set1 Set1 ~> *0 where
    Start :: Witness (P Empty Empty) (P Empty Empty)
    Read :: (Equal Empty {intersect w1 w2}, Equal Empty {intersect w2 (U n Empty)}) =>
                Nat' n
             -> Pair0 (P (Set0 r1) (Set0 w1)) -- Grantee
             -> Pair0 (P (Set0 r2) (Set0 w2)) -- Other
             -> Witness (P {setInsert n r1} w1) (P r2 w2)

r1 = U #2 (U #1 Empty)
w1 = (U #2 (U #5 Empty))
w1' = Empty

r2 = U #3 (U #4 Empty)
w2 = U #3 Empty
w2' = Empty

proc1 = P r1 w1
proc2 = P r2 w2

p = Read #1 proc1 proc2
