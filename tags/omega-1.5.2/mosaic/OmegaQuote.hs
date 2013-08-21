{-# LANGUAGE DataKinds, KindSignatures, QuasiQuotes, GADTs,
             StandaloneDeriving, UnicodeSyntax #-}

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

