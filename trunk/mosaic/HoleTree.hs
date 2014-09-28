{-# LANGUAGE DataKinds, KindSignatures, TypeOperators, GADTs, ScopedTypeVariables, StandaloneDeriving #-}
module HoleTree where

data Nat = Z | S Nat

data Vec :: Nat -> * -> * where
    Nil :: Vec Z a
    (:::) :: a -> Vec n a -> Vec (S n) a

infixr 5 :::

deriving instance Show a => Show (Vec n a)

data HTree :: Nat -> Nat -> * -> * where
    Leaf :: a -> HTree n n a
    Hole :: HTree (S n) n a
    Fork :: HTree m n a -> HTree n o a -> HTree m o a

deriving instance Show a => Show (HTree m n a)

fill :: Vec m a -> HTree m n a -> (HTree o o a, Vec n a)
fill xs (Leaf x) = (Leaf x, xs)
fill (x ::: xs) Hole = (Leaf x, xs)
fill _ Hole = error "Inaccessible"
fill xs (Fork a b) = (Fork a' b', xs'')
    where (a', xs') = fill xs a
          (b', xs'') = fill xs' b

fill0 :: Vec m a -> HTree m Z a -> HTree o o a
fill0 xs a = fst (fill xs a)
