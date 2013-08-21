
data L:: *0 where
  N :: L
  C :: Int -> L -> L
 deriving List(i)

data N:: *0 where
  Zx :: N
  Sx :: N -> N
 deriving Nat(jk)

kind Npair:: *0 where
  P:: Int -> Bool -> Npair
 deriving Pair(i)

ex1 = [2,3,4]i
ex2 = []i
ex7 x = [x,3,x]i
ex8 = ex7 99

ex3 = 2jk
ex4 x = (2+x)jk
ex5 = 0jk
ex9 = ex4 (Sx Zx)


ex6 = (5,True)i

data List :: forall a . a ~> *1 where
   Nil  :: List a
   Cons :: a ~> List a ~> List a
 deriving List(a)

data LIST :: forall a n . n ~> List a ~> *0 where
   NIL  :: LIST Z Nil
   CONS :: a -> LIST n l -> LIST (S n) (Cons a l)
 deriving List(b)

ex10 = [4,True,[2]b,2jk]b


##test "Wrong number of constructors"
 data T:: *0 where
   M:: Int -> T
  deriving List(p)

##test "List name already in use"
 data T:: *0 where
   M:: Int -> T
  deriving List()

##test "Cannot find a List extension called g"
  bad = [34]g
