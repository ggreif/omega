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

kind Usage = VAR | NORMAL

data Tm :: Usage ~> Inventory Tag ~> * where
  -- lambda
  Lm :: Label t -> Tm u [inv; t]i -> Tm NORMAL inv
  -- argument access
  Arg :: Tm VAR [ups; t]i
  Up :: Tm VAR [ups; t]i -> Tm VAR [ups; t, t']i
  -- the lambda introducing the argument
  Enc :: Tm VAR inv -> Tm NORMAL inv
  -- application
  App :: Tm u inv -> Tm v inv -> Tm NORMAL inv
  -- recursive let
  Let :: Label t -> Tm u [inv; t]i ->  Tm v [inv; t]i -> Tm NORMAL inv
 deriving syntax (tm) Nat(Arg, Up) LeftPair(App) Item(Enc)


-- (closed) identity function
--
identity :: Tm NORMAL []i
identity = Lm `a 0tm

-- ($) = \f . \a . f a
--
dollar :: Tm NORMAL []i
dollar = Lm `f (Lm `a (1tm, 0tm)tm)

-- bottom = \n . bottom n
bottom = Lm `n ((0tm), 0tm)tm

-- let a = a in a
leta :: Tm NORMAL []i
leta = Let `a 0tm 0tm
