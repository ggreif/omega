data Dir :: *2 ~> *2 where
  Hor :: name ~> Dir name
  Ver :: name ~> Dir name -- tree of names!

data Tree :: Dir named ~> *1 where
  Unit :: Tree (Ver name)
  Ni :: Tree (Hor name)
  Fork :: Tree (Hor name) ~> Tree (Ver t) ~> Tree (Hor name)
 deriving syntax (tr) LeftList(Ni, Fork) Unit(Unit)
