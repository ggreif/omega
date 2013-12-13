-- "Names Free For Polymorphic Views of Names and Binders" 
-- by Jean-Philippe Bernardy, Nicolas Pouillard
-- http://www.cse.chalmers.se/~bernardy/NamesForFree.pdf

-- originally
--
type Succ a = a `Trunce` ()

data Trunce :: * ~> * ~> * where
  Old :: a -> Trunce a v
  New :: v -> Trunce a v

data Tm :: * ~> * where
  Var :: a -> Tm a
  App :: Tm a -> Tm a -> Tm a
  Lam :: Tm (Succ a) -> Tm a

lam :: (forall v . v -> Tm (a `Trunce` v)) -> Tm a
lam f = Lam (f ())


-- My way??
--
data Tri :: Nat ~> * ~> * where
  Born :: a -> Tri 0t a
  Reach :: Tri n a -> Tri (1+n)t a
