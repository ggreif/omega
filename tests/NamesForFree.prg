-- ref to paper? Nicolas Pouillard

-- originally
--
type Succ a = a `Trunce` ()

data Trunce :: * ~> * ~> * where
  Old :: a -> Trunce a b
  New :: b -> Trunce a b