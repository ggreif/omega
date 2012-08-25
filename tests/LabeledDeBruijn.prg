-- see also http://cs.ioc.ee/~james/papers/Relative_Monads.pdf
-- "Monads Need Not Be Endofunctors"
-- which references Fiore, Plotkin and Turi's work
-- Hamana also has much to say (http://www.cs.gunma-u.ac.jp/~hamana/)
--

-- TODO:
--  o add another parameter (VAR | FUN | NORMAL)
--  o Arg is VAR
--  o Up is VAR -> VAR
--  o Enc is VAR -> FUN
--  o introduce constructor Enc, signifying the function value enclosing the corresponding variable
--    so we can write fak as Lm `fak $ If 0tm == 0 then 1 else App (Enc 0tm) (0tm - 1)

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
identity :: Tm []i
identity = Lm `a 0tm

-- ($) = \f . \a . f a
--
dollar :: Tm []i
dollar = Lm `f (Lm `a (1tm, 0tm)tm)

-- let a = a in a
leta :: Tm []i
leta = Let `a 0tm 0tm
