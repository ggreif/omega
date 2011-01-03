data List :: a ~> *1 where
  Nil  :: List a
  Cons :: a ~> List a ~> List a

data LIST :: n ~> List a ~> *0 where
  NIL  :: LIST Z Nil
  CONS :: a -> LIST n l -> LIST (S n) (Cons a l)

repl :: Nat ~> a ~>  List a
{repl Z x} = Nil
{repl (S n) x} = Cons x {repl n x}

length :: LIST n l -> Nat' n
length NIL = Z
length (CONS x xs) = S (length xs)

lemFromLIST :: Nat' n -> Equal (Cons a as) {repl (S n) a} -> Equal as {repl n a}
lemFromLIST Z Eq = Eq
lemFromLIST (S n) Eq = case lemFromLIST n Eq of Eq -> Eq

lemFromLIST2 :: Nat' n -> Equal a b -> Equal {repl n a} {repl n b}
lemFromLIST2 Z Eq = Eq
lemFromLIST2 (S n) Eq = case lemFromLIST2 n Eq of Eq -> Eq

fromLIST :: LIST n {repl n a} -> [a]
fromLIST NIL = []
fromLIST (CONS x xs) =  (x : fromLIST xs)
 where
  lem = lemFromLIST (length xs)
  lem2 = lemFromLIST2 (length xs)
  theorem lem
  theorem lem2
