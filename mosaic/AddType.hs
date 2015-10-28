{-# LANGUAGE ViewPatterns, KindSignatures, GADTs, PolyKinds, StandaloneDeriving, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, TypeFamilies #-}
{-# LANGUAGE DataKinds, TypeOperators #-} -- 7.10??

module AddType where

data Nat = Z | S Nat deriving Show

plus :: Nat -> Nat -> Nat
plus Z = id
plus (S (plus -> f)) = f . S

data Constr0 (coarg :: Nat) where
  ConstrZ :: Constr0 Z

deriving instance Show (Constr0 Z)

data Constr1 (coarg :: Nat -> Nat) where
  ConstrS :: Constr1 S

deriving instance Show (Constr1 S)

data Plus (arg :: Nat) (coarg :: Nat -> Nat) where
  PlusZ :: Id (f Z) (f Z) -> Plus Z f
  PlusS :: (Plus n `Compose` Constr1) f -> Plus (S n) f
  --        ^^ should this be value inference?

-- Idea: it should be a purely mechanical process to follow the types and create corresponding values,
--       so when the algorithm is encoded in the type, then classes should build inhabitants.
--
class Value a where
  val :: a
  -- val :: Inh a -- <<< better! then PlusS & co become unnecessary (and could be finally tagless)

instance Value (Plus Z f) where
  val = PlusZ Id

instance Value (Plus n f) => Value (Plus (S n) f) where
  val = PlusS $ (val :: Plus n f) `Compose` (val :: Constr1 S)

instance Value (Constr0 Z) where
  val = ConstrZ
instance Value (Constr1 S) where
  val = ConstrS

class Machine (sig :: k -> *) where
  -- have composition, un/tagging, calling (application)
  -- this looks wrong
  app :: (Machine (sig' :: (x -> k) -> *), Machine (sig'' :: x -> *)) => sig' f -> sig'' a -> sig (f a)
  app' :: sig f -> sig a -> sig b
  --app'' :: (Papa f ~ (Papa a -> Papa b)) => sig f -> sig a -> sig b
  appC :: Code f -> Code a -> sig (f b)

-- this fails:
--- *AddType> :t smurf ConstrS `app'` (smurf ConstrZ :: Code Z) :: Code (S Z)
---

data Code (res :: k)
instance Machine (Code)

class Smurf (f :: k -> *) where
  --type Papa f :: k -> *
  --smurf :: f r -> Papa f r
  --smurf :: Machine m => f r -> m (Papa f) -- or even : f r -> m r
  type Papa f :: *
  smurf :: Machine m => f r -> m r

instance Smurf Constr0 where
  type Papa Constr0 = Nat
  smurf ConstrZ = undefined -- Id
instance Smurf Constr1 where
  type Papa Constr1 = Nat -> Nat
  smurf ConstrS = undefined -- Id
instance Smurf (Plus Z) where
  smurf (PlusZ _) = undefined -- Id
--instance Smurf (Plus (S n)) where
--  smurf (PlusS _) = Id

--instance (Value (f a), Value (g b)) => Value ((g b `Compose` f a) c) where

instance (Show (c0 a), Show (c1 a), Value (c0 a), Value (c1 a)) => Value (Match2 c0 c1 a) where
  val = Match2 (val :: c0 a) (val :: c1 a)

deriving instance Show (Plus a c)

data Id (arg :: k) (coarg :: k) where
  Id :: Id x x

deriving instance Show (Id a c)

data Compose (a1 :: (b -> c) -> *) (a0 :: (a -> b) -> *) (coarg :: a -> c) where
  Compose :: (Show (f a), Show (g b)) => g b -> f a -> Compose g f c

deriving instance Show (Compose g f c)

--class Constructor (kind :: k) where

data Match2 (c0 :: k -> *) (c1 :: k -> *) (out :: k) where
  Match2 :: (Show (c0 a), Show (c1 a)) => c0 a -> c1 a -> Match2 c0 c1 a

deriving instance Show (Match2 g f c)

-- Match2 lifts
  --      two    Plus :: Nat -> (Nat -> Nat) -> *
  --      to be  (Match2 (Plus Z)) :: ((Nat -> Nat) -> *) -> (Nat -> Nat) -> *
  --      to be  (Match2 (Plus Z) (Plus (S Z))) :: (Nat -> Nat) -> *
