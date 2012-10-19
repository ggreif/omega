{-# LANGUAGE DataKinds, KindSignatures, QuasiQuotes #-}

import OmegaParser

(°) :: Int -> Int -> Int
a ° b = a + b

-- the iceberg

data Ω :: Int -> * where
  

µ s h = [ω|s * h|]

