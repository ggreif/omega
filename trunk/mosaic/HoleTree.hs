{-# LANGUAGE DataKinds, KindSignatures, TypeOperators, GADTs #-}
module HoleTree where

data Nat = Z | S Nat

data Vec :: Nat -> * -> * where
    Nil :: Vec Z a
    Cons :: a -> Vec n a -> Vec (S n) a

data HTree :: Nat -> Nat -> * -> * where
    Leaf :: a -> HTree n n a
    Hole :: HTree (S n) n a
    Fork :: HTree m n a -> HTree n o a -> HTree m o a

fill :: Vec m a -> HTree m n a -> (HTree n n a, Vec n a)
fill xs (Leaf x) = (Leaf x, xs)
fill (x `Cons` xs) Hole = (Leaf x, xs)
fill xs (Fork a b) =
    case fill xs a of
        (a', xs') -> case fill xs' b of
                        (b', xs'') -> (_, xs'')
{-
fill xs (Fork a b) = (Fork a' b', xs'')
    where (a', xs') = fill xs a
          (b', xs'') = fill xs' b
-}
