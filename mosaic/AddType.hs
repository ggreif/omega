{-# LANGUAGE ViewPatterns, KindSignatures, GADTs, PolyKinds #-}
{-# LANGUAGE DataKinds, TypeOperators #-} -- 7.10??

module AddType where

data Nat = Z | S Nat deriving Show

plus :: Nat -> Nat -> Nat
plus Z = id
plus (S (plus -> f)) = f . S

data Constr0 (coarg :: Nat) where
  ConstrZ :: Constr0 Z

data Constr1 (coarg :: Nat -> Nat) where
  ConstrS :: Constr1 S

data Plus (arg :: Nat) (coarg :: Nat -> Nat) where
  PlusZ :: Id (f Z) (f Z) -> Plus Z f
  PlusS :: (Plus n `Compose` Constr1) f -> Plus (S n) f

data Id (arg :: k) (coarg :: k) where
  Id :: Id x x

data Compose (a1 :: (b -> c) -> *) (a0 :: (a -> b) -> *) (coarg :: a -> c) where
  Compose :: g b -> f a -> Compose b a c

--class Constructor (kind :: k) where