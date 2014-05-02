{-# LANGUAGE DataKinds, KindSignatures #-}

data Nat = Z | S Nat

class LC (rep :: Nat -> *) where
  var :: rep n
  lam :: rep n -> rep n
  app :: rep n -> rep n -> rep n

class TypedLC (rep :: Nat -> *) where
  annot :: rep n -> rep (S n) -> rep n
  typeof :: rep n -> rep (S n)
  arr :: rep (S n) -> rep (S n) -> rep (S n)

class BuiltinLC (rep :: Nat -> *) where
  star :: rep (S (S n))
  int :: rep (S n)
  cnst :: Int -> rep Z


-- ## TESTS ##

t1, t2 :: LC rep => rep Z
t1 = lam var
t2 = t1 `app` t1

t3 :: (LC rep, BuiltinLC rep) => rep Z
t3 = t1 `app` cnst 42

newtype LString (n :: Nat) = L { unL :: String } deriving Show

instance LC LString where
  var = L "?"
  lam body = L $ "(\\" ++ unL body ++ ")"
  app e1 e2 = L $ "(" ++ unL e1 ++ " " ++ unL e2 ++ ")"

instance BuiltinLC LString where
  cnst i = L $ show i
  star = L "*"
