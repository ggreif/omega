import "CurryHoward.prg" (LE, Base, Step)

kind Sign = Negative | Positive

-- 2's complement representation
--
prop Integral :: Sign ~> Nat ~> * where
  Minus :: Nat' (1+n)t -> Integral Negative n
  Plus :: Nat' n -> Integral Positive n


-- LEI is less-than-or-equal on Integral
--
prop LEI :: Sign ~> Nat ~> Sign ~> Nat ~> * where
  NP :: Integral Negative m -> Integral Positive n -> LEI Negative m Positive n
  NN :: LE n m -> Integral Negative m -> Integral Negative n -> LEI Negative m Negative n
  PP :: LE m n -> Integral Positive m -> Integral Positive n -> LEI Positive m Positive n

