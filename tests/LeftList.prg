data Foo :: * where
  Nu :: Foo
  Co :: Foo -> Int -> Foo
 deriving syntax (f) LeftList(Nu, Co)

data Bar = Bnu | Bar Bar Int deriving LeftList(b)

data Baz  :: * where
  Nub :: Baz
  Cob :: Baz -> Int -> Baz
 deriving LeftList(z)


len :: Foo -> Int
len []f = 0
len [rest; _]f = 1 + len rest

t0 = len [[]f; 1, 2, 3]f

t1 = len [lazy [1, 2]f; 3, 4]f

[t2; 4, 5]b = [1,2,3,4,5]b

[[1,2,3]z; 4]z = [[1]z; 2, 3, 4]z

[t3; t4]z = [[1]z; 2]z

##test "these do not match up"
 [[1,2,3]z; 4]z = [[1]z; 2, 3]z

