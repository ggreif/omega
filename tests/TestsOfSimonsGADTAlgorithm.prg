data T:: *0 ~> *0 where
 TI :: T Int
 TB :: T Bool

g:: T a -> a -> Int 
g TI x = x +1
g TB x = 1


data W:: *0 where 
  C:: T a -> a -> W
  
f8:: W -> Bool
f8 (C TB True) = False
f8 (C TI 3) = True
f8 x = False

data V:: *0 where 
  D:: a -> T a -> V

##test "Order matters in refinement"  
 f9:: V -> Bool
 f9 (D True TB) = False
 f9 (D 3 TI) = True
 f9 x = False


g1:: a -> T a -> Int 
g1 x TI = x +1
g1 x TB = 1

g3:: T a -> a -> Int 
g3 TI 3 = 1
 
h:: T a -> [a] -> Int 
h TI (x:xs) = x +1
h TB x = 0

h1:: T a -> [a] -> Int 
h1 TI (x:1:xs) = x +1
h1 TB x = 0

 

##test "Nested Int before GADT match."
  f:: [a] -> T a -> Int 
  f (x:1:xs) TI = x+1

##test "Wrong Constructor"
  bad1:: [a] -> a -> Int
  bad1 TI x = x+1

##test "Expected has too few args"
  bad2:: Int -> a -> Int
  bad2 TI x = x+1

##test "Wrong Constructor 2"
  bad3:: (Int -> Int) -> a -> Int
  bad3 TI x = x+1

##test "Concrete pattern before refinement"
  g2:: a -> T a -> Int 
  g2 3 TI = 1

##test "Nested concrete pattern before refinement"
  f:: [a] -> T a -> Int 
  f (x:1:xs) TI = x+1

mp f [] = []
mp f (x:xs) = f x : (mp f xs)

------------------------------------------
-- Testing smart application and smart let

data Rep:: *0 ~> *0 where
  RI:: Rep Int
  RP:: Rep a -> Rep b -> Rep (a,b)
  
test:: Rep a -> Rep b -> Maybe(Equal a b)
test RI RI = Just Eq
test (RP s1 t1) (RP s2 t2) =
  case test s1 s2 of
    Nothing -> Nothing
    Just Eq -> let s = test t1 t2
               in case s of
                   Nothing -> Nothing
                   Just Eq -> Just Eq
test _ _ = Nothing                
