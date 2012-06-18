-- http://blog.ezyang.com/2010/12/no-one-expects-the-scott-induction/

-- Topic: "smallest infinite ordinal (w)"

kind F = Finite | Infinite

kfix :: (Nat ~> Nat) ~> Nat
{kfix s} = s {kfix s}
type OM = {kfix S}

prop Nat'' :: F ~> Nat ~> * where
  Z' :: Nat'' Finite Z
  S' :: Nat'' f n -> Nat'' f (S n)
  Om :: Nat'' Finite n => Nat'' Infinite OM
 deriving syntax(tn) Nat(Z', S')


allOfThem :: forall (a :: Nat) . Nat'' Finite a => Nat' a -> Nat'' Infinite {kfix S}
allOfThem a = Om
