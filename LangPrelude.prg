-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Thu Mar  3 11:15:06 Pacific Standard Time 2005
-- Omega Interpreter: version 1.0

-- primitives

apply f x = f x          -- f $ g 5 --> apply f (g 5)
compose f g x = f(g x)   -- f . g   --> compose f g
id x = x


data Monad m = 
   Monad (forall a . a -> m a) 
         (forall a b . m a -> (a -> m b) -> m b)
         (forall a . [Char] -> m a)

        
maybeM =  (Monad Just bind fail)
  where return x = Just x
        fail s = Nothing
        bind Nothing g = Nothing
        bind (Just x) g = g x         
        
listM =  (Monad unit bind fail)
  where unit x = [x]
        fail s = []
        bind [] f = []
        bind (x:xs) f = f x ++ bind xs f

ioM = Monad returnIO bindIO failIO

data Eq x y = Eq where x = y

const x _ = x

primitive freshAtom  :: forall (k :: *1) (a::k) . IO(Atom a) 
primitive same  :: forall (k :: *1) (a::k) (b::k).Atom a -> Atom b -> Maybe(Eq a b) 
primitive swapAtom :: forall (k :: *1) (a::k) (b::k) c . Atom a -> Atom b -> c -> c
primitive fuse :: a -> b -> Bind a b
primitive melt :: Bind a b -> IO(a,b)

sameAtom :: forall (k :: *1)(a::k)(b::k).Atom a -> Atom b -> IO(Eq a b)
sameAtom x y = case same x y of
                 Just x -> returnIO x
                 Nothing -> failIO ("Different atoms")

monad ioM

------------------------------------
-- useful list functions

head (x:xs) = x
tail (x:xs) = xs

len [] = 0
len (x:xs) = 1 + len xs

foldr c n []     = n
foldr c n (x:xs) = c x (foldr c n xs)

foldl f acc []     = acc
foldl f acc (x:xs) = foldl f (f acc x) xs

append xs ys = if null xs then ys else (head xs) : (append (tail xs) ys)

lookup x [] = Nothing
lookup x ((y,z):xs) = if x==y then Just z else lookup x xs

member x [] = False
member x (y:ys) = if x==y then True else member x ys

map f [] = []
map f (x:xs) = f x : map f xs

fst (x,y) = x
snd (x,y) = y

max a b = if a >= b then a else b

otherwise = True

----------------------------------

data ContM o i = C ((i -> o) -> o)
unContM (C x) = x

runCont :: ContM i i -> i
runCont m       = unContM m id

contM :: Monad (ContM a)
contM = (Monad return bind fail)
  where return x = C (\k -> k x)
        fail s = error s
        bind (C m) f = C (\k -> m (\i -> unContM (f i) k))
                

