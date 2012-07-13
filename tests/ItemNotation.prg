-- item notation

-- basic: http://www.cedar-forest.org/forest/talks/talks2001/talkPPDP2001.ps
-- extended: http://www.cedar-forest.org/forest/talks/talks2001/microsoft.ps

import "LabeledDeBruijn.prg"

data Itm :: Inventory Tag ~> * where
  -- applicator wagon
  IApp :: Itm inv -> Itm inv -> Itm inv
  -- abstractor wagon
  IAbs :: Label n -> Itm [inv; n]i -> Itm inv
  -- argument access
  IArg :: Itm [ups; t]i
  IUp :: Itm [ups; t]i -> Itm [ups; t, t']i
 deriving syntax (it) Nat(IArg, IUp)

iota :: Tm inv -> Itm inv
iota Arg = IArg
iota (Up m) = IUp (iota m)
iota (Lm n b) = IAbs n (iota b)
iota (App f a) = IApp (iota a) (iota f)

slide1 = iota (Lm `x (Lm `y (1tm,0tm)tm), 0tm)tm  -- assuming `z = 0tm


-- ok now, lets drift to thrists

data Wagon :: Inventory Tag ~> Inventory Tag ~> * where
  AppW :: Wagon inv inv -> Wagon inv inv
  AbsW :: Label n -> Wagon [inv; n]i inv
  ArgW :: Wagon [ups; t]i [ups; t]i
  UpW :: Wagon [ups; t]i [ups; t]i -> Wagon [ups; t, t']i [ups; t, t']i
 deriving syntax (w) Nat(ArgW, UpW) Item(AppW)


data Thrist :: forall (l :: *1) . (l ~> l ~> *)  ~> l ~> l ~> * where
  Nil :: Thrist k a a
  Cons :: k a b -> Thrist k b c -> Thrist k a c
 deriving List(t)


theta :: Tm inv -> exists inv' . Thrist Wagon inv inv'
theta Arg = Ex [ArgW]t
{-
theta (Up m) = Ex [UpW  m']t
    where (Ex thr) = theta m
    	  [m']t = thr
theta (Lm n b) = AbsW n (theta b)
theta (App f a) = AppW (theta a) (theta f)
-}
