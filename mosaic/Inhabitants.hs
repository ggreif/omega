{-# LANGUAGE DataKinds, GADTs, RebindableSyntax #-}

import qualified Prelude as P
import Prelude (Bool (..), ($), error, undefined)

data Nat' = Z' | S' Nat'

data Lam open lev where
  App :: Lam o l -> Lam p l -> Lam False l
  Inh :: Lam True (S' l) ->  (Lam True l -> Lam o l') -> Lam False l'

star :: Lam True (S' (S' Z'))
star = undefined



(>>=) :: Lam True (S' l) -> (Lam True l -> Lam o l') -> Lam False l'
(>>=) = Inh

(&) = App

return :: Lam o l -> Lam False l
return = undefined
fail = error

main' = do int <- star
           i <- int
           j <- int
           -- k <- int & int -- Error: not open, good
           -- sub <- i       -- Error: cannot descend below zero, good
           i & j
