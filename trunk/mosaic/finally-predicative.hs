{-# LANGUAGE DataKinds, KindSignatures, FlexibleContexts, StandaloneDeriving
           , UndecidableInstances, FlexibleInstances #-}

data Nat = Z | S Nat

class LC (rep :: Nat -> *) where
  var :: rep n
  lam :: rep n -> rep n
  app :: rep n -> rep n -> rep n

class TypedLC (rep :: Nat -> *) where
  annot :: rep n -> rep (S n) -> rep n
  typeof :: rep n -> rep (S n)
  arr :: rep (S n) -> rep (S n) -> rep (S n)
  pi' :: rep (S n) -> rep (S n)

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

instance {-HasLevel (LString n) => -}LC LString where
  var = {-addLevel $-} L "?"
  lam body = L $ "(\\" ++ unL body ++ ")"
  app e1 e2 = L $ "(" ++ unL e1 ++ " " ++ unL e2 ++ ")"

class HasLevel p where
  addLevel :: p -> p
  level :: p -> Int

instance HasLevel (LString Z) where
  addLevel p = L $ unL p ++ "@" ++ (show . level) p
  level _ = 0

instance HasLevel (LString n) => HasLevel (LString (S n)) where
  addLevel p = L $ unL p ++ "@" ++ (show . level) p
  level _ = 1

instance BuiltinLC LString where
  cnst i = L $ show i
  star = L "*"

instance TypedLC LString where
  --pi

newtype TypeOf (rep :: Nat -> *) (n :: Nat) = T { unT :: rep (S n) }

deriving instance Show (rep (S n)) => Show (TypeOf rep n)

instance (LC rep, TypedLC rep) => LC (TypeOf rep) where
  var = T var
  lam (T body) = T $ pi' body

-- ugly workaround to simulate Pi
--pi' :: rep (S n) -> rep n
--pi' :: rep (S n) -> rep (S n)
--pi' = undefined
