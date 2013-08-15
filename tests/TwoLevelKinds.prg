data Dir :: *2 where
  Hor :: Dir
  Ver :: Dir

{-
data TreeF :: * ~> Dir ~> *1 where
  Unit :: TreeF f Ver
  Ni :: TreeF f Hor
  Fork :: f ~> TreeF f Hor ~> TreeF f Hor
 deriving syntax (tr) List(Ni, Fork) Unit(Unit)

--kind Id d k = Id k

kind Fix t f = In (f (Fix t f))

type Tree = Fix TreeF
-}


data T a = Nix | F a a

data Fix f = Fix (f (Fix f))

type Tree = Fix T
