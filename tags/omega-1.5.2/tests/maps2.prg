id x = x
mapL f [] = []
mapL f (x:xs) = f x : mapL f xs

Ftree :: (* ~> *) ~> * ~> *
data Ftree f a = Tip a | Fork (f (Ftree f a))

mapF :: (forall a b . (a -> b) -> f a -> f b) -> (x -> y) -> Ftree f x -> Ftree f y 
mapF map f (Tip x) = Tip(f x)
mapF map f (Fork x) = Fork (map (mapF map f) x)

--------------------------------------------------------

data Rep :: forall (k:: *1) . *1 ~> k ~> *0 where
   Int :: Rep *0 Int
   List :: Rep (*0 ~> *0) []
   Ftree :: Rep ((*0 ~> *0) ~> *0 ~> *0) Ftree
   Ap :: forall (k1:: *1) (s:: *1) (f:: k1 ~> s) (x:: k1) .
         (Rep (k1 ~> s) f) -> (Rep k1 x) -> Rep s (f x)

 

data Rl :: forall (u:: *1) (v:: *1) . *1 ~> u ~> v ~> *0 ~> *0 where
   Star :: Rl *0 m n (m -> n)
   Arr :: forall (k1:: *1) (k2:: *1) (t1:: k1 ~> k2) (t2:: k1 ~> k2) 
                 (alpha:: k1) (beta:: k1) r s .
                 (Rl k1 alpha beta r) -> 
                 (Rl k2 (t1 alpha) (t2 beta) s) -> 
                 (Rl (k1 ~> k2) t1 t2 (r -> s))


x = 0

map :: forall (k:: *1) (t:: k) a . Rl k t t a -> Rep k t -> a
map Star Int = id
map (Arr Star Star) List = mapL
map (w@Star) (Ap List Int) = (map (Arr Star Star) List) (map Star Int)

--map (Arr (Arr Star Star) (Arr Star Star)) Ftree = mapF
-- the problem with this is that the "a" in (Rl k t t a) isn't
-- polymorphic enough. It returns: 
-- ((a -> b) -> (t a) -> s b) -> (c -> d) -> (f t c) -> g s d)
-- but it needs to be
-- (forall a b . (a -> b) -> (t a) -> s b) -> (c -> d) -> (f t c) -> g s d)

ex1 =  map (Arr Star Star) List (\ x -> x+1) [2,3,4]

---------------------------------------------------------


data Rep2 :: forall (k:: *1) . k ~> *0 where
   Int2 :: Rep2 Int
   List2 :: Rep2 []
   Ap2 :: forall (f:: *0 ~> *0) x . (Rep2 f) -> (Rep2 x) -> Rep2 (f x)
   