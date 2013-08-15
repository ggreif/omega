data Dir :: *2 where
  Hor :: Dir
  Ver :: Dir


data Tree :: Dir ~> *1 where
  Unit :: Tree Ver
  Ni :: Tree Hor
  Fork :: Tree d ~> Tree Hor ~> Tree Hor
 deriving syntax (tr) List(Ni, Fork) Unit(Unit)

