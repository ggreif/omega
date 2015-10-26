{-# LANGUAGE ViewPatterns, KindSignatures, GADTs, PolyKinds #-}

module AddType where

data Nat = Z | S Nat deriving Show

plus :: Nat -> Nat -> Nat
plus Z = id
plus (S (plus -> f)) = f . S

data Constr1 (coarg :: Nat -> Nat) where
  ConstrS :: Constr1 S

data Plus (arg :: Nat) (coarg :: Nat -> Nat) where
  PlusZ :: Id (f Z) (f Z) -> Plus Z f
  PlusS :: (Plus n `Compose` Constr1) f -> Plus (S n) f

data Id (arg :: k) (coarg :: k) where
  Id :: Id x x

data Compose (a1 :: (b -> c) -> *) (a0 :: (a -> b) -> *) (coarg :: a -> c) where
  --Compose
