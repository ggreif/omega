{-# LANGUAGE DataKinds, GADTs, KindSignatures, RebindableSyntax #-}

import qualified Prelude as P
import Prelude (Bool (..), ($), error, undefined)

data Nat' = Z' | S' Nat'

data Lam open lev where
  App :: Lam o l -> Lam p l -> Lam False l
  Inh :: Lam True (S' l) ->  (Lam True l -> Lam o l') -> Lam False l'
  Star :: Lam True (S' (S' n))
  Close :: Lam o l -> Lam False l

class Inhabitable (ent :: Bool -> Nat' -> *) where
  starN :: ent True (S' (S' n))
  inhabit :: ent True (S' l) ->  (ent True l -> ent o l') -> ent False l'
  isle :: ent o l -> ent False (S' l)


instance Inhabitable Lam where
  starN = Star
  inhabit = Inh
  isle Star = Close Star
  isle (Close a) = isle a

star :: Lam True (S' (S' Z'))
star = starN



(>>=) :: Inhabitable ent => ent True (S' l) -> (ent True l -> ent o l') -> ent False l'
(>>=) = inhabit

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
