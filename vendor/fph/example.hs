
data List a where 
 Nil :: List a 
 Cons :: a -> List a -> List a

data T a where 
 MkT :: T a

data Unit where 
 Unit :: Unit 

 -- GHC ticket 1123

out :: forall a. T a -> Unit
out = \x -> Unit

inHoisted :: forall r. Unit -> (forall a. T a -> r) -> r
inHoisted = \x -> \foo -> foo MkT

inUnhoisted :: Unit -> forall r. (forall a. T a -> r) -> r
inUnhoisted = \x -> \foo -> foo MkT

testHoisted :: Unit
testHoisted = inHoisted Unit out

testUnhoisted :: Unit
testUnhoisted = inUnhoisted Unit out


-- GHC ticket 1330 

n0 = \f -> \z -> z

n1 :: (forall a. (a -> a) -> a -> a)
n1 = \f -> \z -> f z

nsucc :: (forall a. (a -> a) -> a -> a) -> (forall a. (a -> a) -> a -> a)
nsucc = \n -> \f -> \z -> f (n f z)

add :: (forall a. (a -> a) -> a -> a) -> (forall a. (a -> a) -> a -> a) -> (forall a. (a -> a) -> a -> a)
add m n = \f -> \a -> m f (n f a)

mul :: (forall a. (a -> a) -> a -> a) -> (forall a. (a -> a) -> a -> a) -> (forall a. (a -> a) -> a -> a)
mul m n = \f -> \a -> m (n f) a

-- already works with GHC 6.4
exp0 :: (forall a. (a -> a) -> a -> a) -> (forall a. (a -> a) -> a -> a) -> (forall a. (a -> a) -> a -> a)
exp0 m n = n m


exp2 :: (forall a. (a -> a) -> a -> a) -> (forall a. (a -> a) -> a -> a) -> (forall a. (a -> a) -> a -> a)
exp2 m n = (n (mul m) n1)

 -- random tests 
id = \x -> x 

foo :: forall a. List a 
foo = Nil

ids :: List (forall a. a -> a) 
ids = Nil

goo :: (forall a. a -> a) -> Int -> Int 
goo x = x 

app :: forall a b. (a -> b) -> a -> b 
revapp :: forall a b. a -> (a -> b) -> b 

blah1 = goo id
blah2 = app goo id

twice :: forall a. (a -> a) -> a -> a 
twice = \f -> \x -> f (f x) 

ghh = twice id 

mkList :: List (forall a. a -> a) 
mkList = Nil

bar' :: List (forall a. a -> a) 
bar' = (Cons (\x -> x) ids)

head :: forall a. List a -> a 

runHR :: forall b. (forall a. a -> a) -> b -> b
runHR x y = x y


bog1 = app runHR (\x -> x) 
bog2 = revapp (\x -> x) runHR 


-- join test 
f1 :: forall a b. a -> b 
f2 :: forall a. a -> a 

f4 :: List (forall a. a -> a) 

choose :: forall a. a -> a -> a

goh = choose f1 f2 

choose0 :: forall a. a -> List a -> a 

goh1 :: (forall a. a -> a)
goh1 = choose0 f1 f4

-- a lot of combinators, demonstrates also boxy instantiation
guh = runHR (head ids)
guh1 = app runHR (app (\x -> x) (revapp ids head))

gah :: List (forall a. a -> a) -> Unit
gah x = Unit

exmpl1 = gah ids
exmpl2 = gah (id ids)


-- example: 
exmp3  = Cons (Cons id Nil) Nil
exmp3a :: List (List (forall a. a -> a))
exmp3a =  (Cons (Cons id Nil) Nil)
 
blaho :: (forall a. a -> a) -> (forall a. a ->a)
blaho = id (choose id)

-- examples of boxy instantiation 
boxinst1 = head ids 
boxinst2 = head ids 3 
