prop A :: * where
  Try :: DiffLabel a b => A

prop B :: Tag ~> Tag ~> * where
  Free :: DiffLabel a b -> B a b

prop C :: Tag ~> Row Tag * ~> * where
  Triv :: C a {}r
  Step :: DiffLabel a b -> C a r -> C a {b=Int; r}r
  Step' :: DiffLabel a b => C a r -> C a {b=Int; r}r
