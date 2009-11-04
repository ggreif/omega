import "LangPrelude.prg"

prop A :: * where
  Try :: DiffLabel a b => A

prop B :: Tag ~> Tag ~> * where
  Free :: DiffLabel a b -> B a b

prop C :: Tag ~> Row Tag * ~> * where
  Triv :: C a {}r
  Step :: DiffLabel a b -> C a r -> C a {b=Int; r}r
  Step' :: DiffLabel a b => C a r -> C a {b=Int; r}r

--prop (!=) (x::*1) (x::*1) = primitive

--prop (!=) :: *1 ~> *1 ~> *0 where
--  Really :: (!=) a b

test1 = Step d Triv where
          d = case sameLabel `a `b of
              R d -> d

test2 = Step' (Step' Triv)

