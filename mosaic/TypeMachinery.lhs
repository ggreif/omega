Here we define all the stuff that is needed for our singleton
types:
 - phantom types (when GHC 7.4 arrives, the user-defined kinds)
 - corresponding singleton types

These are basically the constructs from Omega,
reimplemented in Haskell for our purposes.

> {-# LANGUAGE GADTs, KindSignatures, StandaloneDeriving,
>              RankNTypes, TypeFamilies, FlexibleInstances #-}
> module TypeMachinery where

The natural numbers:
 o first the phantom types

> data Z; data S n

 o the using the above the singleton type Nat'

> data Nat' :: * -> * where
>   Z :: Nat' Z
>   S :: Nat' n -> Nat' (S n)

> deriving instance Show (Nat' a)

Type-level addition

> type family Plus m n :: *
> type instance Plus Z n = n
> type instance Plus (S m) n = S (Plus m n)

Nat' addition

> plus :: Nat' a -> Nat' b -> Nat' (Plus a b)
> plus Z n = n
> plus (S m) n = S (plus m n)

A data type for existentially hiding
(e.g.) Nat' values

> data Hidden :: (* -> *) -> * where
>   Hide :: Show (a n) => a n -> Hidden a

> deriving instance Show (Hidden t)

> toNat' :: Integral i => i -> Hidden Nat'
> toNat' 0 = Hide Z
> toNat' n = case toNat' (n - 1) of
>            Hide n -> Hide (S n)

Now we are ready to make Hidden Nat' an Integral type

> instance Eq (Hidden Nat')
> instance Ord (Hidden Nat')
> instance Enum (Hidden Nat')
> instance Num (Hidden Nat')
> instance Real (Hidden Nat')

> instance Integral (Hidden Nat') where
> toInteger (Hide Z) = 0

