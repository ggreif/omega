-- Note: this is a heavily simplified testcase

data Dir :: *2 where
  Hor :: Dir
  Ver :: Dir

data Tree :: Dir ~> *1 where
  Unit :: Tree Ver
  Ni :: Tree Hor
  Fork :: Tree d ~> Tree Hor ~> Tree Hor
 deriving syntax (tr) List(Ni, Fork) Unit(Unit)


graft :: Tree d ~> Tree f ~> Tree f
{graft what ()tr} = what
--{graft []tr ()tr} = []tr -- this is rejected


{- NOTE: we have an Omega bug here:

prompt> :norm {graft []tr ()tr}
Normalizes to:
  []tr

prompt> :kind []tr
[]tr :: Tree Hor  = []tr

prompt> :kind {graft []tr ()tr}
{graft []tr ()tr} :: Tree Ver  = {graft []tr ()tr}

... BUT: Hor /= Ver :-(
-}
