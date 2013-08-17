data Dir :: *2 where
  Hor :: name ~> Dir -- these are nodes
  Ver :: name ~> Dir -- should be tree of names!

data Tree :: Dir ~> *1 where
  Pri :: Tag ~> Tree (Hor Tag)
  Unit :: Tree (Ver name)
  Ni :: Tree (Hor name)
  Fork :: Tree (d Tag) ~> Tree (Hor name) ~> Tree (Hor name)
 deriving syntax (tr) List(Ni, Fork) Unit(Unit) Item(Pri)

data Tree' :: Tree d ~> * where
  Labeled :: Label tag -> Tree' (tag)tr
  In :: Tree' ()tr
  Fork :: Tree' head -> Tree' tail -> Tree' [head; tail]tr
  Done :: Tree' []tr
 deriving syntax (ar) List(Done, Fork) Unit(In) Item(Labeled)

kind Wrap a = W a

data Stack :: Tree (d Tag) ~> Tree (e Tag) ~> * where
  Cell :: Stack ()tr ()tr
  NicheDone :: Stack ()tr []tr
  Niche :: Stack tr out -> Stack tr [out]tr
  Also :: Tree' at -> Stack tr out' -> Stack tr out -> Stack tr [out'; out]tr
 deriving syntax(z) Record(NicheDone, Also)

t1 = {(`hey)ar=Cell}z