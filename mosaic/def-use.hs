{-# LANGUAGE DataKinds, KindSignatures, RankNTypes, StandaloneDeriving, GADTs, TypeOperators
           , FlexibleInstances, ViewPatterns, UndecidableInstances #-}


import Data.Char

--                    var intro     lambda body             v--- app ---v
data Place' = Root' | Def' Place' | Body' Place' | Lunder' Place' | Runder' Place'

class KnownPlace (p :: Place') where
  thePlace :: Place p

-- value inference for a place type
instance KnownPlace Root' where thePlace = Root
instance KnownPlace p => KnownPlace (Def' p) where thePlace = Def
instance KnownPlace p => KnownPlace (Body' p) where thePlace = Body
instance KnownPlace p => KnownPlace (Lunder' p) where thePlace = Lunder
instance KnownPlace p => KnownPlace (Runder' p) where thePlace = Runder

-- singleton type isomorphic to (promoted) kind Place'
data Place :: Place' -> * where
  Root :: Place Root'
  Def :: KnownPlace p => Place (Def' p)
  Body :: KnownPlace p => Place (Body' p)
  Lunder :: KnownPlace p => Place (Lunder' p)
  Runder :: KnownPlace p => Place (Runder' p)

deriving instance Show (Place p)


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
type PlusFive n = S' (PlusFour n)
type PlusTen n = PlusFive (PlusFive n)


----------- def       use
data Lam :: Place' -> Place' -> * where
  Dummy :: (KnownPlace d, KnownPlace u) => Lam d u -- only for Show!
  L :: (KnownPlace d, KnownPlace u) => ((forall u . KnownPlace u => Lam (Def' d) u) -> Lam (Def' d) u) -> Lam d u
  (:&) :: (KnownPlace d, KnownPlace d', KnownPlace d'', KnownPlace u) => Lam d' (Lunder' d) -> Lam d'' (Runder' d) -> Lam d u

instance Show (Lam def use) where
  show lam@(L f) = "(\\" ++ show (f Dummy) ++ ")" ++ duStr lam
  show all@(f :& a) = "(" ++ show f ++ " & " ++ show a ++ ")" ++ duStr all
  show d@Dummy = duStr d

duStr :: forall def use . (KnownPlace def, KnownPlace use) => Lam def use -> String
duStr l = "d" ++ place2str (def l) ++ "u" ++ place2str (use l)
  where place2str :: Place p -> String
        place2str = filter isUpper . show

def :: KnownPlace def => Lam def use -> Place def
def _ = thePlace
use :: KnownPlace use => Lam def use -> Place use
use _ = thePlace

nat2int :: Nat n -> Int
nat2int Z = 0
nat2int (S n) = nat2int n + 1

nat2str = show . nat2int

test :: Lam Root' (Lunder' Root')
test = L (\a -> a :& a)
test' :: Lam Root' Root'
test' = L $ \x->x
test'' :: Lam Root' Root'
test'' = L $ \x->L $ \x->x
