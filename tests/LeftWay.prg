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

t5 [[1,2,3]z; 4]z = 42

##test "these do not match up"
 t6 = t5 [[1]z; 2, 3]z


data Roo = Ru | Rest Roo Int Char  deriving LeftRecord(lr)

t7 = {}lr

t8 = {t7; 42='j'}lr

t9 = {42='j'}lr

t10 = {42='j', 25='g'}lr

t11 = {t8; 42='j', 25='g'}lr

data LPair = Pa a Int deriving LeftPair(lp)

t12 = ('l', 42)lp

t13 = ('l', 25, 42)lp

t14 = (t13, 66)lp

data LLPair = LPa a Int deriving LeftPair(llp)

t15 = (t14, 7)llp

t16 = case show t15 of {"('l',25,42,66,7)llp" -> "bad"; "(('l',25,42,66)lp,7)llp" -> "good"}

verify "good" = True

##test "issue 81"
  v1 = verify t16

