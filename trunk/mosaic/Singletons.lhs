> module Singletons where

The twist is that t appears below in
a type and (promoted) kind position.

> class Singleton t where
>   data Sng t :: t -> *

An example

> data Nat = Z' | S' Nat

> instance Singleton Nat where
>   data Sng Nat :: Nat -> * where
>     Z :: Sng Nat Z'
>     S :: Sng Nat n -> Sng Nat (S' n)

Then we can typedef it:

> type Nat' n = Sng Nat
