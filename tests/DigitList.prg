import "../src/LangPrelude.prg" (maybeM)
import "Inventory.prg"

monad maybeM

data Fin :: Nat ~> *0 where
  Fz :: Fin (S m)
  Fs :: Fin m -> Fin (S m)
 deriving Nat(f)


data DigitList :: Nat ~> *0 where
  None :: DigitList a
  Longer :: DigitList a -> Fin a -> DigitList a
 deriving LeftList(dl)


up :: Nat' (2+b)t -> DigitList (2+b)t -> DigitList (2+b)t
up _ []dl = [1f]dl
up b [bla; f]dl = case tryIncr b f of
                  Nothing -> [up b bla; 0f]dl
                  Just d -> [bla; d]dl

tryIncr :: Nat' (2+b)t -> Fin (2+b)t -> Maybe (Fin (2+b)t)
tryIncr 2v 1f = Nothing
tryIncr (2+v)v 0f = Just 1f
tryIncr (3+v)v 1f = Just 2f
tryIncr (3+v)v (1+f)f = do { i <- tryIncr (2+v)v f; return (1+i)f }

data Fin' :: Nat ~> Nat ~> *0 where
  Fz' :: Fin' (S m) Z
  Fs' :: Fin' m n -> Fin' (S m) (S n)
 deriving Nat(fp)

data DigitList' :: Nat ~> Inventory Nat ~> *0 where
  None' :: DigitList' a []i
  Longer' :: DigitList' a inv -> Fin' a t -> DigitList' a [inv; t]i
 deriving LeftList(dlp)

