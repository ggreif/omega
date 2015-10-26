{-# LANGUAGE ViewPatterns, KindSignatures, GADTs, PolyKinds, StandaloneDeriving, FlexibleInstances #-}
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

-- TODO: Match2 should lift
  --      two    Plus :: Nat -> (Nat -> Nat) -> *
  --      to be  (Match2 Plus) :: (Nat -> *) -> (Nat -> Nat) -> *