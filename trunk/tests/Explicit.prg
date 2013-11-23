-- See Uustalu, Ghani, Hamana (Explicit...)

kind Discipline = Regular | Explicit

data Calc :: Discipline ~> * ~> * where
  Var :: a -> Calc Regular a
  App :: Calc d a -> Calc d a -> Calc d a
  Abs :: Calc d a -> Calc d (Maybe a)

-- define Explicit to Regular conv
-- define ev. (Krivine etc.)

