data Pat :: *4 where
  Y :: Pat
  Q :: Pat ~> Pat
 deriving Nat(p)

data Pat' :: Pat ~> *3 where
  Y' :: Pat' Y
  Q' :: Pat' n ~> Pat' (Q n)
 deriving Nat(q)

data Pat'' :: Pat' a ~> *2 where
  Y'' :: Pat'' Y'
  Q'' :: Pat'' m ~> Pat'' (Q' m)
 deriving Nat(r)

data Pat''' :: forall a (b::Pat' a) . Pat'' b ~> *1 where
  Y''' :: Pat''' Y''
  Q''' :: Pat''' w ~> Pat''' (Q'' w)
 deriving Nat(s)


data Pat'''' :: forall a (b::Pat' a) (c::Pat'' b) . Pat''' c ~> * where
  Y :: Pat'''' Y'''
  Q :: Pat'''' z -> Pat'''' (Q''' z)
 deriving Nat(u)

plus :: Pat ~> Pat ~> Pat
{plus 0p n} = n
{plus (1+m)p n} = {plus m (1+n)p}

plus' :: Pat' a ~> Pat' b ~> Pat' {plus a b}
{plus' 0q n} = n
{plus' (1+m)q n} = {plus' m (1+n)q}

plus'' :: forall a (a'::Pat' a) b (b'::Pat' b) . Pat'' a' ~> Pat'' b' ~> Pat'' {plus' a' b'}
{plus'' 0r n} = n
{plus'' (1+m)r n} = {plus'' m (1+n)r}

plus''' :: forall a (a'::Pat' a) (a''::Pat'' a') b (b'::Pat' b) (b''::Pat'' b') . Pat''' a'' ~> Pat''' b'' ~> Pat''' {plus'' a'' b''}
{plus''' 0s n} = n
{plus''' (1+m)s n} = {plus''' m (1+n)s}

pl :: forall a (a'::Pat' a) (a''::Pat'' a') (a'''::Pat''' a'') b (b'::Pat' b) (b''::Pat'' b') (b'''::Pat''' b'') . Pat'''' a''' -> Pat'''' b''' -> Pat'''' {plus''' a''' b'''}
pl 0u n = n
pl (1+m)u n = pl m (1+n)u

