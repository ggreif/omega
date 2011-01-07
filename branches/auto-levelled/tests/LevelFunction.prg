data Pat :: *2 where
  Y :: Pat
  Q :: Pat ~> Pat
 deriving Nat(p)

data Pat' :: Pat ~> *1 where
  Y' :: Pat' Y
  Q' :: Pat' n ~> Pat' (Q n)
 deriving Nat(q)

data Pat'' :: Pat' a ~> * where
  Y :: Pat'' Y'
  Q :: Pat'' n -> Pat'' (Q' n)
 deriving Nat(r)

plus :: Pat ~> Pat ~> Pat
{plus 0p n} = n
{plus (1+m)p n} = {plus m (1+n)p}

plus' :: Pat' a ~> Pat' b ~> Pat' {plus a b}
{plus' 0q n} = n
{plus' (1+m)q n} = {plus' m (1+n)q}

pl :: Pat'' a -> Pat'' b -> Pat'' {plus' a b}
pl 0r n = n
pl (1+m)r n = pl m (1+n)r

-- TESTS --

t1 :: Pat'' 25q
t1 = pl 13r 12r

