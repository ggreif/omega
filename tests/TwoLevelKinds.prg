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


kind T r a = Nix | F r a r

kind Fix f a = X (f (Fix f a) a)
                  ^
------------------+
--- here is the bug!

type Tree a = Fix T a

{- Triggers omega bug:

omega.exe: RankN.hs:(1704,1)-(1708,23): Non-exhaustive patterns in function matchKind

-}
