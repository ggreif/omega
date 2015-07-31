{-# LANGUAGE DataKinds, KindSignatures, QuasiQuotes, GADTs,
             StandaloneDeriving, UnicodeSyntax #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies, TypeOperators, PolyKinds
           , MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}

import OmegaParser
import InhabitantTH

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
instance (b °° a) => Just b °° Maybe a
--instance (k °° a) => Just k °° Maybe a

class (a :: k) °°° (b :: * -> *) | a -> b
instance Nothing °°° Maybe
--instance (Nothing :: Maybe k) °°° Maybe

data Stuff a b where
  Full :: (a °° b) => Stuff a b
  Part :: (a °°° b) => Stuff a (b c)

deriving instance Show (Stuff a b)

[d|data H|] -- standalone
id [d|data H'|] -- also works

dataRewrite
  [d| data A where B :: A; C :: B
    |]

