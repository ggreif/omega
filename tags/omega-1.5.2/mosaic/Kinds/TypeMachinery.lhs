Here we define all the stuff that is needed for our singleton
types:
 - types of user-defined kinds
 - corresponding singleton types

These are basically the constructs from Omega,
reimplemented in Haskell for our purposes.

> {-# LANGUAGE GADTs, KindSignatures, StandaloneDeriving,
>              RankNTypes, TypeFamilies, FlexibleInstances,
>              PolyKinds, DataKinds, IncoherentInstances #-}
> module Kinds.TypeMachinery where

The natural numbers:
 o first the type level

> data Nat = Zt | St Nat

 o then (using the above) the singleton type Nat'

> data Nat' :: Nat -> * where
>   Z :: Nat' Zt
>   S :: Nat' n -> Nat' (St n)

> deriving instance Show (Nat' a)

Type-level addition

> type family Plus (m :: Nat) (n :: Nat) :: Nat
> type instance Plus Zt n = n
> type instance Plus (St m) n = St (Plus m n)

Nat' addition

> plus :: Nat' a -> Nat' b -> Nat' (Plus a b)
> plus Z n = n
> plus (S m) n = S (plus m n)

Equality on Nat'

> sameNat' :: Nat' a -> Nat' b -> Bool
> sameNat' Z Z = True
> sameNat' (S m) (S n) = sameNat' m n
> sameNat' _ _ = False

A data type for existentially hiding
(e.g.) Nat' values

> data Hidden :: (k -> *) -> * where
>   Hide :: Show (a n) => a n -> Hidden a

> deriving instance Show (Hidden t)

> toNat' :: Integral i => i -> Hidden Nat'
> toNat' 0 = Hide Z
> toNat' n = case toNat' (n - 1) of
>            Hide n -> Hide (S n)

Now we are ready to make Hidden Nat' an Integral type

> instance Eq (Hidden Nat') where
>   Hide a == Hide b = sameNat' a b

> instance Ord (Hidden Nat') where
>   Hide Z `compare` Hide Z = EQ
>   Hide Z `compare` Hide _ = LT
>   Hide _ `compare` Hide Z = GT
>   Hide (S m) `compare` Hide (S n) = Hide m `compare` Hide n

> instance Enum (Hidden Nat') where
>   toEnum = toEnum . fromIntegral
>   fromEnum = fromIntegral

> instance Num (Hidden Nat') where
>   fromInteger = toNat'
>   signum (Hide Z) = 0
>   signum _ = 1
>   abs n = n
>   Hide a + Hide b = Hide $ plus a b
>   a * b = fromInteger $ toInteger a * toInteger b

> instance Real (Hidden Nat') where
>   toRational = toRational . toInteger

> instance Integral (Hidden Nat') where
>   toInteger (Hide Z) = 0
>   toInteger (Hide (S n)) = 1 + toInteger (Hide n)
>   quotRem a b = let (a', b') = toInteger a `quotRem` toInteger b in (fromInteger a', fromInteger b')

McBride's Fin data type. By counting backwards from the
result index, it only admits a fixed number of inhabitants.

> data Fin :: Nat -> * where
>   Stop :: Fin (St Zt)
>   Retreat :: Fin s -> Fin (St s)

> deriving instance Show (Fin a)

