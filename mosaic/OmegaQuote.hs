{-# LANGUAGE DataKinds, KindSignatures, QuasiQuotes, GADTs,
             StandaloneDeriving #-}

import OmegaParser

(°) :: Int -> Int -> Int
a ° b = a + b

-- the iceberg

data Ω :: * -> * where
  Berg :: Ω a
  Δ :: Ω a
  Int :: Int -> Ω Int

deriving instance Show (Ω a)

µ s h = [ω|s * h|]

a = µ 1 2

c = [ω|33|]

