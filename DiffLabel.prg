prop A :: * where
  Try :: DiffLabel a b => A

prop B :: Tag ~> Tag ~> * where
  Free :: DiffLabel a b -> B a b
