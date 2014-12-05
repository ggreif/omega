{-# LANGUAGE DataKinds, KindSignatures, RankNTypes, StandaloneDeriving, GADTs, TypeOperators
           , FlexibleInstances, ViewPatterns, UndecidableInstances #-}

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

type PlusFour n = S' (S' (S' (S' n)))
type PlusFive n = S' (S' (S' (S' (S' n))))


----------- def     use
data Lam :: Nat' -> Nat' -> * where
  L :: (KnownNat d, KnownNat u') => ((forall u . KnownNat u => Lam (S' d) u) -> Lam d u') -> Lam d u'
  (:&) :: (KnownNat d, KnownNat d', KnownNat d'', KnownNat u) => (Lam d' (PlusFour d)) -> (Lam d'' (PlusFive d)) -> Lam d u

instance Show (Lam def use) where
  show lam@(L f) = "(\\"++show (f undefined)++")"++duStr lam
  show all@(f :& a) = "("++duStr f++"&"++duStr a++")"++duStr all

duStr :: forall def use . (KnownNat def, KnownNat use) => Lam def use -> String
duStr l = "d" ++ show (nat2int $ def l) ++ "u" ++ show (nat2int $ use l)

def :: KnownNat def => Lam def use -> Nat def
def _ = theNat
use :: KnownNat use => Lam def use -> Nat use
use _ = theNat

nat2int :: Nat n -> Int
nat2int Z = 0
nat2int (S (nat2int -> n)) = n + 1

test :: Lam Z' Z'
test = L (\a -> a :& a)
