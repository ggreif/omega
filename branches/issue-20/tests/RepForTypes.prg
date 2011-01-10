data Monad m = 
   Monad (forall a . a -> m a) 
         (forall a b . m a -> (a -> m b) -> m b)
         (forall a . [Char] -> m a)

return x = Just x
fail s = Nothing
bind Nothing g = Nothing
bind (Just x) g = g x
        
id x = x

data Equal :: *0 ~> *0 ~> *0 where
   Eq :: (b -> b) -> (b -> b) -> Equal b b
      
self = Eq id id

data Rep :: *0 ~> *0 where
   Rint :: Rep Int
   Rchar :: Rep Char
   Runit :: Rep ()
   Rpair :: (Rep a) -> (Rep b) -> Rep ((a,b))
   Rsum :: (Rep a) -> (Rep b) -> Rep ((a+b))
   Rcon :: ([Char]) -> (Rep t) -> Rep t
   Rdata :: (Rep i) -> (t -> i) -> (i -> t) -> Rep t

test :: Rep a -> Rep b -> Maybe (Equal a b)
test Rint Rint = return self
test Rchar Rchar = return self
test Runit Runit = return self
test (Rpair x y) (Rpair a b) =
  do { Eq f g <- test x a; Eq h i <- test y b; return self }
test (Rsum x y) (Rsum a b) =
  do { Eq f g <- test x a; Eq h i <- test y b; return self }
test (Rcon s x) (Rcon c y) =
  if eqStr s c then test x y else Nothing
test _ _ = Nothing


list :: Rep a -> Rep [a]
list x = Rdata (Rsum (Rcon "[]" Runit) (Rcon ":" (Rpair x (lazy (list x))))) h g
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
sum (Rcon s r) x = sum r x
sum _ x = 0

fst(x,y) = x
snd (x,y) = y

sum2 :: Rep a -> Code a -> Code Int
sum2 Rint x = x
sum2 Runit x = [| 0 |]
sum2 (Rpair x y) z = [| $(sum2 x [| fst $z |]) + $(sum2 y [| snd $z |]) |]
sum2 (Rsum r s) x = [| case $x of
                         L m -> $(sum2 r [| m |])
                         R m -> $(sum2 s [| m |]) |]
                              
sum3 x = [| \ w -> $(sum2 x [| w |]) |]

r1 = Rpair Rint (Rsum Rint Runit)

