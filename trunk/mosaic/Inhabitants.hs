{-# LANGUAGE DataKinds, GADTs, RebindableSyntax #-}

import qualified Prelude as P


data Nat' = Z' | S' Nat'

--data Nat = 

data Lam l = App (Lam l) (Lam l) | Inh (Lam (S' l)) (Lam l -> Lam l)

star :: Lam (S' Z')
star = P.undefined



(>>=) :: Lam (S' l) -> (Lam l -> Lam l) -> Lam l
(>>=) = Inh

return a = a
fail = P.error

main' = do i <- star
           i
           