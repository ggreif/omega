data Pat :: *4 where
  Q :: Pat ~> Pat

data Pat' :: Pat ~> *3 where
  Q' :: Pat' n ~> Pat' (Q n)

data Pat'' :: Pat' a ~> *2 where
  Q'' :: Pat'' m ~> Pat'' (Q' m)

--data Pat''' :: forall a (b::Pat' a) . Pat'' b ~> *1 where
data Pat''' :: Pat'' b ~> *1 where
  Q''' :: Pat''' w ~> Pat''' (Q'' w)

