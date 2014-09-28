{-# LANGUAGE GADTs, KindSignatures, DataKinds #-}
module TwoHoles where

data Nat = Z | S Nat

data Tree a = Node (Tree a) (Tree a) | Leaf a
  deriving Show

data TreeWithHoles :: Nat -> Nat -> * -> * where
  HLeaf :: a -> TreeWithHoles n n a
  HNode :: TreeWithHoles m n a -> TreeWithHoles n o a -> TreeWithHoles m o a
  Hole  :: TreeWithHoles (S n) n a

type TreeWith1Hole  a = TreeWithHoles (S Z) Z a
type TreeWith2Holes a = TreeWithHoles (S (S Z)) Z a

data Vec :: Nat -> * -> * where
  (:::) :: a -> Vec n a -> Vec (S n) a
  Nil   :: Vec Z a

fill :: TreeWithHoles n Z a -> Vec n a -> Tree a
fill t xs = fst (fill' t xs)

fill' :: TreeWithHoles m n a -> Vec m a -> (Tree a, Vec n a)
fill' Hole        (x ::: xs) = (Leaf x, xs)
fill' (HLeaf x)          xs  = (Leaf x, xs)
fill' (HNode l r)        xs  =
  case fill' l xs of
    (l', ys) -> case fill' r ys of
       (r', zs) -> (Node l' r', zs)
--
fill' Hole               _   = error "inaccessible"

  
