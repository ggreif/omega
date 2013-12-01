-- see also http://cs.ioc.ee/~james/papers/Relative_Monads.pdf
-- "Monads Need Not Be Endofunctors"
-- which references Fiore, Plotkin and Turi's work
-- Hamana also has much to say (http://www.cs.gunma-u.ac.jp/~hamana/)
--

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

{- THIS IS NOT READY YET!
sink :: Tag ~> Nat ~> Inventory Tag
{sink t 0t} = [inv; t]i
{sink t (1+n)t} = [{sink t n}; t']i

prop Tm' :: Inventory Tag ~> * where
  Arg' :: Tm' inv -> Label t -> Tm' [inv; t]i

varLemma :: Label t -> Nat' n -> Tm' {sink t n} -> exists (inv :: Inventory Tag) (t' :: Tag) . Tm' [inv; t']i
varLemma t 0v = undefined

var :: Label t -> Nat' n -> Tm {sink t n}
var l 0v = 0tm
var l 1v = Up $ var l 0v
var l 2v = Up $ var l 1v
var l 3v = Up $ var l 2v
--var l (1+v)v = Up $  (var l v)
--  where theorem hyp = varLemma l v
-}

-- (closed) identity function
--
identity :: Tm NORMAL []i
identity = Lm `a 0tm

-- ($) = \f . \a . f a
--
---dollar :: Tm NORMAL []i
---dollar = Lm `f (Lm `a (var `f 1v, var `a 0v)tm)

-- bottom = \n . bottom n
bottom = Lm `n ((0tm)tm, 0tm)tm

-- y = \a . a a
y = Lm `a ((0tm)tm, (0tm)tm)tm

-- let a = a in a
leta :: Tm NORMAL []i
leta = Let `a 0tm 0tm
