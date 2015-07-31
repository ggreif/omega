{-# LANGUAGE DataKinds, KindSignatures, QuasiQuotes, GADTs,
             StandaloneDeriving, UnicodeSyntax #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies, TypeOperators, PolyKinds
           , MultiParamTypeClasses, FunctionalDependencies #-}

import OmegaParser

(°) :: Int -> Int -> Int
a ° b = a + b

-- Ω values

data Ω :: * -> * where
  Bottom :: Ω a  -- (⊥)
  Int :: Int -> Ω Int
  Apply :: Ω (a -> b) -> Ω a -> Ω b -- (⋅)
deriving instance Show (Ω a)

(⋅) = Apply
(⊥) = Bottom

µ s h = [ω|s * h|]

a = µ 1 2

c = [ω|33|]

c1 = [e|33|]
c2 = [e||id 33||]

stuff = [d| data Nat = Z | S Nat |]
data Nat = Z | S Nat deriving Show

--refinementPlus =
refined
  [d| plus :: (a ° Nat) -> (b ° Nat) -> (a `plus` b ° Nat)
      Z `plus` n = n
      (S m) `plus` n = S (m `plus` n)
    |]

--refined refinementPlus

class (a :: k) °° (b :: *) | a -> b

instance True °° Bool
instance False °° Bool

instance Z °° Nat
instance S n °° Nat

--instance (Nothing :: Maybe k) °° Maybe a
--instance ((b :: k) °° a) => Just b °° Maybe a
--instance (k °° a) => Just k °° Maybe a

refined
  [d| data A where B :: A; C :: B
    |]
