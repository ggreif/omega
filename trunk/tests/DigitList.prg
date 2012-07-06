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
  where tryIncr :: Nat' (1+b)t -> Fin (1+b)t -> Maybe (Fin (1+b)t)
        tryIncr 2v 1f = Nothing
        tryIncr (2+v)v 0f = Just 1f
        tryIncr (2+v)v (1+f)f = do { i <- tryIncr (1+v)v f; return (1+i)f }

nup :: Nat' (2+b)t -> Int -> DigitList (2+b)t -> DigitList (2+b)t
nup _ 0 dl = dl
nup b n dl = nup b (n - 1) (up b dl)


-- same with reflected types
--
data Fin' :: Nat ~> Nat ~> *0 where
  Fz' :: Fin' (S m) Z
  Fs' :: Fin' m n -> Fin' (S m) (S n)
 deriving Nat(fp)

data DigitList' :: Nat ~> Inventory Nat ~> *0 where
  None' :: DigitList' a []i
  Longer' :: DigitList' a inv -> Fin' a t -> DigitList' a [inv; t]i
 deriving LeftList(dlp)


upInv :: Nat ~> Inventory Nat ~> Inventory Nat
{upInv b []i} = [1t]i
{upInv (1+b)t [rest; b]i} = [{upInv (1+b)t rest}; 0t]i
{upInv (2+b)t [rest; a]i} = [rest; (1+a)t]i

up' :: Nat' (2+b)t -> DigitList' (2+b)t i -> DigitList' (2+b)t {upInv (2+b)t i}
up' _ []dlp = [1fp]dlp
up' b [bla; f]dlp = case tryIncr b f of
                    L Eq -> [up' b bla; 0fp]dlp
                    R d -> [bla; d]dlp
  where tryIncr :: Nat' (1+b)t -> Fin' (1+b)t a -> (Equal (1+b)t (1+a)t + Fin' (1+b)t (1+a)t)
        tryIncr 2v 1fp = L Eq
        tryIncr (2+v)v 0fp = R 1fp
        tryIncr (2+v)v (1+f)fp = case tryIncr (1+v)v f of
                                  L Eq -> L Eq
                                  R i -> R (1+i)fp
