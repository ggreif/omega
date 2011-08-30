data Appl :: * where
  Var :: Label t -> Appl
  App :: Appl -> Appl -> Appl
  Lam :: Label t -> Appl -> Appl
  -- In :: Appl -- don't use
  Let :: Label t -> Appl -> Appl -> Appl
 deriving syntax(ac) Applicative(Var, App, Lam, Let) -- Record(In, Let)

