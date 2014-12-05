{-# LANGUAGE DataKinds, KindSignatures, RankNTypes, StandaloneDeriving, GADTs, TypeOperators, FlexibleInstances, ViewPatterns, UndecidableInstances #-}

--import qualified GHC.TypeLits as L
--import GHC.TypeLits (type (+))


data Nat' = Z' | S' Nat'

data Nat :: Nat' -> * where
  Z :: Nat Z'
  S :: Nat n -> Nat (S' n)

class KnownNat (n :: Nat') where
  theNat :: Nat n

instance KnownNat Z' where
  theNat = Z

instance KnownNat n => KnownNat (S' n) where
  theNat = S theNat

deriving instance Show (Nat n)

-- Def-Use markers

----------- def     use
data Lam :: Nat' -> Nat' -> * where
  L :: (Lam a b -> Lam a b) -> Lam a b
  (:&) :: Lam a b -> Lam a b -> Lam a b



test :: Lam Z' Z'
test = L (\a -> a :& a)
