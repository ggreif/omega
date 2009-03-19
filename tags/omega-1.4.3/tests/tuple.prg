kind RowT = Nil | Cons *0 RowT

data Tuple :: RowT ~> *0 where
   Unit :: Tuple Nil
   Pair :: a -> (Tuple as) -> Tuple (Cons a as)


data Rw :: a ~> b ~> *1 where
   Rnil :: Rw x y
   Rcons :: x ~> y ~> Rw x y ~> Rw x y
 deriving Record(rw) 

data Recrd :: Rw *0 *0 ~> *0 where
   Recnil :: Recrd Rnil
   Reccons :: a -> b -> Recrd r -> Recrd (Rcons a b r)
 deriving Record(rc)

test = { `a=5, `b=True}rc
test2 = {"a"=23, "b"="zxc"}rc
test3 = {`name="tim", `age = 21}