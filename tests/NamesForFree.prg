-- "Names Free For Polymorphic Views of Names and Binders" 
-- by Jean-Philippe Bernardy, Nicolas Pouillard
-- http://www.cse.chalmers.se/~bernardy/NamesForFree.pdf

-- originally
--
type Succ a = a `Trunce` ()

data Trunce :: * ~> * ~> * where
  Old :: a -> Trunce a b
  New :: b -> Trunce a b