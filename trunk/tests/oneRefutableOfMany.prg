data Elem:: *1 where
 Bot:: Elem
 A:: Elem
 B:: Elem
 C:: Elem
 D:: Elem
 E:: Elem

data Elem':: Elem ~> *0 where
 A':: Elem' A
 B':: Elem' B
 C':: Elem' C
 D':: Elem' D
 E':: Elem' E
 
prop LT:: Elem ~> Elem ~> *0 where
 Bot_ :: LT Bot x
 A_B :: LT A B
 B_C :: LT B C
 C_D :: LT C D
 E_ :: LT x E 
 -- Trans :: LT a b -> LT b c -> LT a c
 
data Se:: Nat ~> Elem ~> *0 where
 Em:: Se Z Bot
 Ad :: LT b a => Elem' a -> Se n b -> Se (S n) a

x = 2

##test "One refutable of many"
  ans = Ad D' (Ad E' Em)
