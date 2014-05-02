{-# LANGUAGE DataKinds, KindSignatures, FlexibleContexts, StandaloneDeriving
           , UndecidableInstances, FlexibleInstances, OverloadedStrings
           , GADTs, PatternSynonyms #-}

import Data.String
import Data.Function
import Unsafe.Coerce

data Nat = Z | S Nat
data Cardinality = Finite | Infinite 

data N :: Cardinality -> Nat -> * where
  Z' :: N Finite Z
  S' :: N Finite n -> N Finite (S n)
  O' :: N Infinite n -> N Infinite (S n)

deriving instance Show (N c n)

pattern Omega o = O' o

type Nat' n = N Finite n

omega = fix (unsafeCoerce O' :: N Infinite (S n) -> N Infinite (S n))

test :: N Infinite (S n) -> N Infinite n
test (Omega ii) = ii

class LC (rep :: Nat -> *) where
  var :: rep n
  lam :: rep n -> rep n
  app :: rep n -> rep n -> rep n

class TypedLC (rep :: Nat -> *) where
  annot :: rep n -> rep (S n) -> rep n
  typeof :: rep n -> rep (S n)
  arr :: rep (S n) -> rep (S n) -> rep (S n) -- NONO! see pi'
  pi' :: rep (S n) -> rep (S n)

class BuiltinLC (rep :: Nat -> *) where
  star :: rep (S (S n))
  int :: rep (S n)
  cnst :: Int -> rep Z

-- ##############
--     TypeOf
-- ##############

instance (LC rep, TypedLC rep) => LC (TypeOf rep) where
  var = T var
  lam (T body) = T $ pi' body

instance BuiltinLC rep => TypedLC (TypeOf rep) where
  pi' _ = T star

instance BuiltinLC rep => BuiltinLC (TypeOf rep) where
  star = T star
  int = T star
  cnst _ = T int


-- ## TESTS ##

t1, t2 :: LC rep => rep Z
t1 = lam var
t2 = t1 `app` t1

t3 :: (LC rep, BuiltinLC rep) => rep Z
t3 = t1 `app` cnst 42

newtype LString (n :: Nat) = L { unL :: String } deriving Show
instance IsString (LString n) where
  fromString = L

instance {-HasLevel (LString n) => -}LC LString where
  var = {-addLevel $-} "?"
  lam body = L $ "(\\ " ++ unL body ++ ")"
  app e1 e2 = L $ "(" ++ unL e1 ++ " " ++ unL e2 ++ ")"

{-
class HasLevel p where
  addLevel :: p -> p
  level :: p -> Int

instance HasLevel (LString Z) where
  addLevel p = unL p ++ "@" ++ (show . level) p
  level _ = 0

instance HasLevel (LString n) => HasLevel (LString (S n)) where
  addLevel p = unL p ++ "@" ++ (show . level) p
  level _ = 1
-}

instance BuiltinLC LString where
  cnst i = L $ show i
  star = "*"
  int = "Int"

instance TypedLC LString where
  pi' body = L $ "(|| " ++ unL body ++ ")"

newtype TypeOf (rep :: Nat -> *) (n :: Nat) = T { unT :: rep (S n) }

deriving instance Show (rep (S n)) => Show (TypeOf rep n)
