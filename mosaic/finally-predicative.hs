{-# LANGUAGE DataKinds, KindSignatures, FlexibleContexts, StandaloneDeriving
           , UndecidableInstances, FlexibleInstances, OverloadedStrings
           , GADTs, PatternSynonyms, TypeFamilies, RankNTypes #-}

import Data.String
import Data.Function
import Unsafe.Coerce
import Prelude hiding (succ)

data Nat = Z | S Nat
data Cardinality = Finite | Infinite

-- Alternative: Use Maybe Nat for the storeys
type family Climb (n :: Maybe Nat) :: Maybe Nat where
  Climb Nothing = Nothing
  Climb (Just (S n)) = Just n

type family Succ (n :: Maybe Nat) :: Maybe Nat where
  Succ Nothing = Nothing
  Succ (Just n) = Just (S n)

type family Min (l :: Maybe Nat) (r :: Maybe Nat) :: Maybe Nat where
  Min Nothing r = r
  Min l Nothing = l
  Min (Just Z) r = Just Z
  Min l (Just Z) = Just Z
  Min (Just (S l)) (Just (S r)) = Just (S (NatMin l r))

type family NatMin (l :: Nat) (r :: Nat) :: Nat where
  NatMin Z r = Z
  NatMin l Z = Z
  NatMin (S l) (S r) = S (NatMin l r)

type UZ = Just Z

type family Norm (unat :: Maybe Nat) :: Maybe Nat where
  Norm UZ = UZ
  Norm Nothing = Nothing

class Card (rep :: Maybe Nat -> *) where
  zero :: rep UZ
  succ :: rep p -> rep (Succ p)

newtype UNatStr (sem :: Maybe Nat) = UNatStr String deriving Show
instance Card UNatStr where
  zero = UNatStr "0"
  succ (UNatStr p) = UNatStr $ 'S' : p

data UNat (sem :: Maybe Nat) where
  Ze :: UNat (Just Z)
  Su :: UNat (Just n) -> UNat (Just (S n))
  Inf :: UNat Nothing

instance Card UNat where
  zero = Ze
  succ Ze = Su Ze
  succ (Su a) = Su (Su a)
  succ Inf = Inf

deriving instance Show (UNat sem)


data Tw (ord :: Cardinality) (from :: Nat) (to :: Nat) = Tw (N Finite from) (N ord to) deriving Show

--type family Up tw where
--  Up (Tw Finite n (S m)) = Tw Finite (S n) m
--  Up (Tw Infinite n (S m)) = Tw Infinite (S n) m

up :: Tw ord from (S to) -> Tw ord (S from) to
up (Tw n (S' m)) = Tw (S' n) m
up (Tw n (Omega m)) = Tw (S' n) m

data N :: Cardinality -> Nat -> * where
  Z' :: N Finite Z
  S' :: N Finite n -> N Finite (S n)
  O' :: N Infinite n -> N Infinite (S n)

deriving instance Show (N c n)

type family Omega where
  Omega = S Omega

pattern Omega o = O' o

type Nat' n = N Finite n

omega = fix (unsafeCoerce O' :: N Infinite (S n) -> N Infinite (S n))

test :: N Infinite (S n) -> N Infinite n
test (Omega ii) = ii

class LC (rep :: Nat -> Nat -> *) where
  var :: rep n m
  lam :: rep n m -> rep n m
  app :: rep n m -> rep n m -> rep n m -- FIX upper

class TypedLC (rep :: Nat -> Nat -> *) where
  annot :: rep n m -> rep (S n) m -> rep n m
  typeof :: rep n (S m) -> rep (S n) m
  --arr :: rep (S n) -> rep (S n) -> rep (S n) -- NONO! see pi'
  pi' :: rep (S n) m -> rep (S n) m

class BuiltinLC (rep :: Nat -> Nat -> *) where
  star :: rep (S (S n)) m
  int :: rep (S n) m
  cnst :: Int -> rep Z m

-- ##############
--     TypeOf
-- ##############

newtype TypeOf (rep :: Nat -> Nat -> *) (n :: Nat) (m :: Nat) = T { unT :: rep (S n) m }

deriving instance Show (rep (S n) m) => Show (TypeOf rep n m)

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

t1, t2 :: LC rep => rep Z m
t1 = lam var
t2 = t1 `app` t1

t3 :: (LC rep, BuiltinLC rep) => rep Z m
t3 = t1 `app` cnst 42

newtype LString (n :: Nat) (m :: Nat) = L { unL :: String } deriving Show
instance IsString (LString n m) where
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


instance LC (Tw c) where
  --var = Tw undefined omega
