{-# LANGUAGE DataKinds, GADTs, RebindableSyntax #-}

import qualified Prelude as P
import Prelude (($), error, undefined)

data Nat' = Z' | S' Nat'

--data Nat = 

data Lam l = App (Lam l) (Lam l) | Inh (Lam (S' l)) (Lam l -> Lam l)

star :: Lam (S' (S' Z'))
star = undefined



(>>=) :: Lam (S' l) -> (Lam l -> Lam l) -> Lam l
(>>=) = Inh

(&) = App

return :: Lam l -> Lam (S' l)
return a = a
fail = error

main' = do int <- star
           i <- int
           int -- return $ i & i
           