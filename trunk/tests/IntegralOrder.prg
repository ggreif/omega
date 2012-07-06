import "CurryHoward.prg" (LE, tryLE, maybeM)

kind Signed = Negative Nat | Positive Nat

-- 2's complement representation
--
prop Integral :: Signed ~> * where
  Minus :: Nat' (1+n)t -> Integral (Negative (1+n)t)
  Plus :: Nat' n -> Integral (Positive n)


-- LEI is less-than-or-equal on Integral
--
prop LEI :: Signed ~> Signed ~> * where
  NP :: LEI (Negative m) (Positive n)
  NN :: LE n m -> Integral (Negative m) -> Integral (Negative n) -> LEI (Negative m) (Negative n)
  PP :: LE m n -> Integral (Positive m) -> Integral (Positive n) -> LEI (Positive m) (Positive n)

monad maybeM

tryLEI :: Integral s1 -> Integral s2 -> Maybe (LEI s1 s2)
tryLEI (Minus _) (Plus _) = Just NP
tryLEI (a@Minus a') (b@Minus b') = do le <- tryLE b' a'
                                      return (NN le a b)
tryLEI (a@Plus a') (b@Plus b') = do le <- tryLE a' b'
                                    return (PP le a b)
tryLEI _ _ = Nothing
