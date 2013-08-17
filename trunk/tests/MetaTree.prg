data Dir :: *2 where
  Hor :: name ~> Dir
  Ver :: name ~> Dir -- tree of names!

data Tree :: Dir ~> *1 where
  Unit :: Tree (Ver name)
  Ni :: Tree (Hor name)
  Fork :: Tree (d name) ~> Tree (Hor name) ~> Tree (Hor name)
 deriving syntax (tr) List(Ni, Fork) Unit(Unit)

data Tree' :: Tree d ~> * where
  In :: Tree' ()tr
  Fork :: Tree' head -> Tree' tail -> Tree' [head; tail]tr
  Done :: Tree' []tr
 deriving syntax (ar) List(Done, Fork) Unit(In)

data Stack :: Tree d ~> Tree e ~> * where
  NicheDone :: Stack ()tr []tr
  Niche :: Stack tr out -> Stack tr [out]tr
  Also :: Tree' at -> Stack tr out' -> Stack tr out -> Stack tr [out'; out]tr

 deriving syntax(z) Record(NicheDone, Also)
