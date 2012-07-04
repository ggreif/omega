

data Inventory :: *1 ~> *1 where
  Empty :: Inventory a
  More :: Inventory a ~> a ~> Inventory a
 deriving LeftList(i)
