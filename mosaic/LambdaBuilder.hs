{-# LANGUAGE KindSignatures, DataKinds, TypeOperators, StandaloneDeriving, GADTs #-}

-- See: https://code.google.com/p/omega/wiki/LambdaGraph

data {-kind-} Lam = Var Lam | App Lam Lam | Abs Lam | Ref [Go]
data {-kind-} Go = Up | Le | Ri

class Builder (shape :: Lam -> *) where
  v :: shape inner -> shape (Var inner)
  lam :: shape inner -> shape (Abs inner)
  app :: shape left -> shape right -> shape (App left right)
  here :: shape (Ref '[Up])
  up :: shape (Ref p) -> shape (Ref (Up ': p))

data Classical :: Lam -> * where
  LAM :: Classical sh -> Classical (Abs sh)
  APP :: Classical left -> Classical right -> Classical (App left right)
  VAR :: Classical sh -> Classical (Var sh)
  HERE :: Classical (Ref '[Up])

deriving instance Show (Classical sh)

instance Builder Classical where
  lam = LAM
  app = APP
  v = VAR
  here = HERE
