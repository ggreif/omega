{-# LANGUAGE DataKinds, KindSignatures, RankNTypes, StandaloneDeriving, GADTs, TypeOperators, FlexibleInstances, ViewPatterns, UndecidableInstances #-}

import qualified GHC.TypeLits as L
import GHC.TypeLits (type (+))


data Nat' = Z' | S' Nat'

data Nat :: Nat' -> * where
  Z :: Nat 0
  S :: Nat n -> Nat (1+n)

class KnownNat (n :: L.Nat) where
  theNat :: Nat n

instance KnownNat 0 where
  theNat = Z

instance (KnownNat n, m ~ (1+n)) => KnownNat m where
  theNat = S theNat

deriving instance Show (Nat n)

-- Def-Use markers

