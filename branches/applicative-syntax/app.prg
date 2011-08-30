data Appl :: * where
  App :: Appl -> Appl -> Appl
  Var :: Label t -> Appl
  Lam :: Label t -> Appl -> Appl
  In :: Appl -- don't use
  Let :: Label t -> Appl -> Appl -> Appl
 deriving syntax(ac) Applicative(App) Record(In, Let)

