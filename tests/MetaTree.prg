data Dir :: *2 where
  Hor :: name ~> Dir
  Ver :: name ~> Dir -- tree of names!

data Tree :: Dir ~> *1 where
  Unit :: Tree (Ver name)
  Ni :: Tree (Hor name)
  Fork :: Tree (Hor name) ~> Tree (d name) ~> Tree (Hor name)
 deriving syntax (tr) LeftList(Ni, Fork) Unit(Unit)
