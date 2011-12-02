Here we define all the stuff that is needed for our singleton
types:
 - phantom types (when GHC 7.4 arrives, the user-defined kinds)
 - corresponding singleton types

These are basically the constructs from Omega,
reimplemented in Haskell for our purposes.

> {-# LANGUAGE GADTs, KindSignatures, StandaloneDeriving #-}
> module TypeMachinery where

The natural numbers:
 o first the phantom types

> data Z; data S n

 o the using the above the singleton type Nat'

> data Nat' :: * -> * where
>   Z :: Nat' Z
>   S :: Nat' n -> Nat' (S n)

> deriving instance Show (Nat' a)
