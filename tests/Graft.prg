data Dir :: *2 where
  Hor :: Dir
  Ver :: Dir

data Tree :: Dir ~> *1 where
  Unit :: Tree Ver
  Ni :: Tree Hor
  Fork :: Tree d ~> Tree Hor ~> Tree Hor
 deriving syntax (tr) List(Ni, Fork) Unit(Unit)


-- graft WHAT      WHERE     IN
graft :: Tree d ~> Tree e ~> Tree f ~> Tree f
{graft what ()tr ()tr} = what
{graft what []tr tr} = tr
{graft what [head'; tail']tr [head; tail]tr} = [{graft what head' head}; {graft what tail' tail}]tr


{- NOTE: we have an Omega bug here:

prompt> :norm {graft []tr ()tr ()tr}
Normalizes to:
  []tr

prompt> :kind []tr
[]tr :: Tree Hor  = []tr

prompt> :kind {graft []tr ()tr ()tr}
{graft []tr ()tr ()tr} :: Tree Ver  = {graft []tr ()tr ()tr}

... BUT: Hor /= Ver :-(
-}
