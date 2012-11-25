import "../tests/OneHi.prg" (plus, plusS)

data Thrist :: (l ~> l ~> *) ~> l ~> l ~> * where
  Nil :: Thrist k a a
  Cons :: k a b -> Thrist k b c -> Thrist k a c
 deriving List(t)


data At :: * ~> Nat ~> Nat ~> * where
  HoldChar :: Char -> At Char n (S n)


move :: Nat' offs -> Nat' len -> Thrist (At Char) here {plus len here} -> Thrist (At Char) offs {plus len offs}
move _ Z Nil = Nil
move offs (1+len)v (Cons (HoldChar c) as) = Cons (HoldChar c) $ move (1+offs)v len as
  where theorem plusS
