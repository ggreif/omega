-- item notation

-- basic: http://www.cedar-forest.org/forest/talks/talks2001/talkPPDP2001.ps
-- extended: http://www.cedar-forest.org/forest/talks/talks2001/microsoft.ps

import "LabeledDeBruijn.prg"

data Itm :: Inventory Tag ~> * where
  -- applicator wagon
  AppW :: Itm inv -> Itm inv -> Itm inv
  -- abstractor wagon
  AbsW :: Label n -> Itm [inv; n]i -> Itm inv
  -- argument access
  IArg :: Itm [ups; t]i
  IUp :: Itm [ups; t]i -> Itm [ups; t, t']i
 deriving syntax (it) Nat(IArg, IUp)

iota :: Tm inv -> Itm inv
iota Arg = IArg
iota (Up m) = IUp (iota m)
iota (Up m) = IUp (iota m)
iota (Lm n b) = AbsW n (iota b)
iota (App f a) = AppW (iota a) (iota f)

slide1 = iota (Lm `x (Lm `y (1tm,0tm)tm), 0tm)tm  -- assuming `z = 0tm

