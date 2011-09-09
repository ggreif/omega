-- testing all kinds of backquoted constructs
--


-- value level
--

data Cons = Cons Int Int

foo (a `Cons` b) = a + b + b

check42 42 = "good"

t1 = check42 $ foo (Cons 2 20)


-- type level
--

data Baz :: * ~> * ~> * where
  Quux :: Int `Baz` Int

bar :: * ~> *
{bar (Int `Baz` b)} = b
{bar (Baz Int Int)} = Int
