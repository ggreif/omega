data Appl :: * where
  Var :: Label t -> Appl
  App :: Appl -> Appl -> Appl
  Lam :: Label t -> Appl -> Appl
  Let :: Label t -> Appl -> Appl -> Appl
 deriving syntax(ac) Applicative(Var, App, Lam, Let)

