{-# LANGUAGE DataKinds, KindSignatures, QuasiQuotes, GADTs #-}

import OmegaParser

(°) :: Int -> Int -> Int
a ° b = a + b

-- the iceberg

data Ω :: Int -> * where
  Berg :: Ω a
  Δ :: Ω a
  

µ s h = [ω|s * h|]

a = µ 1 2

