{-# LANGUAGE KindSignatures, DataKinds, TypeOperators #-}

data {-kind-} Lam = Var Lam | App Lam Lam | Abs Lam | Ref [Go]
data {-kind-} Go = Up | Le | Ri

class Builder (shape :: Lam -> *) where
  v :: shape inner -> shape (Var inner)
  lam :: shape inner -> shape (Abs inner)
  app :: shape left -> shape right -> shape (App left right)
  here :: shape (Ref '[Up])
  up :: shape (Ref p) -> shape (Ref (Up ': p))