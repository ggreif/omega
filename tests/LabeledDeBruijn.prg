import "Inventory.prg"

data Tm :: Inventory Tag ~> * where
  -- lambda
  Lm :: Label t -> Tm [inv; t]i -> Tm inv
  -- argument access
  Arg :: Tm [ups; t]i
  Up :: Tm [ups; t]i -> Tm [ups; t, t']i
  -- application
  App :: Tm inv -> Tm inv -> Tm inv
  -- recursive let
  Let :: Label t -> Tm [inv; t]i ->  Tm [inv; t]i -> Tm inv
 deriving syntax (tm) Nat(Arg, Up) LeftPair(App)


-- identity function
--
id :: Tm []i
id = Lm `a 0tm

-- ($) = \f . \a . f a
--
dollar :: Tm []i
dollar = Lm `f (Lm `a (1tm, 0tm)tm)

-- let a = a in a
leta :: Tm []i
leta = Let `a 0tm 0tm
