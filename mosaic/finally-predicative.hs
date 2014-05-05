{-# LANGUAGE DataKinds, KindSignatures, FlexibleContexts, StandaloneDeriving
           , UndecidableInstances, FlexibleInstances, OverloadedStrings
           , GADTs, PatternSynonyms, TypeFamilies, RankNTypes #-}

import Data.String
import Data.Function
import Unsafe.Coerce
import Prelude hiding (succ)

data Nat = Z | S Nat deriving Show

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

type family NatMax (l :: Nat) (r :: Nat) :: Nat where
  NatMax Z r = r
  NatMax l Z = l
  NatMax (S l) (S r) = S (NatMax l r)

type UZ = Just Z

class Card (rep :: Maybe Nat -> *) where
  infty :: rep Nothing
  zero :: rep UZ
  succ :: rep p -> rep (Succ p)

newtype UNatStr (sem :: Maybe Nat) = UNatStr String deriving Show
instance Card UNatStr where
  infty = UNatStr "oo"
  zero = UNatStr "0"
  succ (UNatStr p) = UNatStr $ 'S' : p

data UNat (sem :: Maybe Nat) where
  Ze :: UNat (Just Z)
  Su :: UNat (Just n) -> UNat (Just (S n))
  Inf :: UNat Nothing

instance Card UNat where
  infty = Inf
  zero = Ze
  succ Ze = Su Ze
  succ (Su a) = Su (Su a)
  succ Inf = Inf

deriving instance Show (UNat sem)

data Tw (from :: Nat) (to :: Maybe Nat) = Tw (Nat' from) (UNat to) deriving Show

up :: Tw from to -> Tw (S from) (Climb to)
up (Tw n m) = Tw (S' n) (pred m)
  where pred :: UNat m -> UNat (Climb m)
        pred Inf = Inf
        pred (Su p) = p

data Nat' :: Nat -> * where
  Z' :: Nat' Z
  S' :: Nat' n -> Nat' (S n)

deriving instance Show (Nat' n)

-- --------------+ at  -+ room
                 v      v
class LC (rep :: Nat -> Maybe Nat -> *) where
  var :: rep n m
  lam :: rep n m -> rep n m
  app :: rep n m -> rep n' m' -> rep (NatMax n n') (Min m m')

class TypedLC (rep :: Nat -> Maybe Nat -> *) where
  annot :: rep n m -> rep (S n) m -> rep n m
  typeof :: rep n m -> rep (S n) (Climb m)
  --arr :: rep (S n) -> rep (S n) -> rep (S n) -- NONO! see pi'
  pi' :: rep (S n) m -> rep (S n) m

class BuiltinLC (rep :: Nat -> Maybe Nat -> *) where
  star :: rep (S (S n)) Nothing
  int :: rep (S n) Nothing
  io :: rep (S Z) UZ
  cnst :: Int -> rep Z Nothing

-- ##############
--     TypeOf
-- ##############

newtype TypeOf (rep :: Nat -> Maybe Nat -> *) (n :: Nat) (m :: Maybe Nat) = T (rep (S n) Nothing) -- So far all type-y result things are unbounded

deriving instance Show (rep (S n) Nothing) => Show (TypeOf rep n m)

instance (LC rep, TypedLC rep, BuiltinLC rep) => LC (TypeOf rep) where
  var = T int
  lam (T body) = T $ pi' body
  app (T f) (T e) = T $ f `app` e

instance BuiltinLC rep => TypedLC (TypeOf rep) where
  pi' body = body

instance (BuiltinLC rep, TypedLC rep) => BuiltinLC (TypeOf rep) where
  star = T star
  int = T star
  cnst _ = T int
  io = T $ pi' star


-- ## TESTS ##

t1, t2 :: LC rep => rep Z Nothing
t1 = lam var
t2 = t1 `app` t1

t3 :: (LC rep, BuiltinLC rep) => rep Z Nothing
t3 = t1 `app` cnst 42

t4 :: (LC rep, BuiltinLC rep) => rep (S Z) UZ
t4 = io `app` int

newtype LString (n :: Nat) (m :: Maybe Nat) = L { unL :: String } deriving Show
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
  io = "IO"

instance TypedLC LString where
  pi' body = L $ "(|| " ++ unL body ++ ")"


instance LC Tw where
  var = Tw undefined undefined -- Inf
