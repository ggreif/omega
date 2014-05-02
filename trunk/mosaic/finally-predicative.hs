{-# LANGUAGE DataKinds, KindSignatures #-}

--import GHC.TypeLits

data Nat = Z | S Nat

class LC (rep :: Nat -> *) where
  star :: rep (S (S n))
  int :: rep (S n)
  arr :: rep (S n) -> rep (S n) -> rep (S n)
  cnst :: Int -> rep Z
  var :: rep n
  lam :: rep n -> rep n
  app :: rep n -> rep n -> rep n
  annot :: rep n -> rep (S n) -> rep n
