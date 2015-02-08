{-# LANGUAGE DataKinds, GADTs, KindSignatures, RebindableSyntax #-}

import qualified Prelude as P
import Prelude (Show (..), Bool (..), ($), error, undefined, const, (.))
import Data.List

data Nat' = Z' | S' Nat'

class Inhabitable (ent :: Bool -> Nat' -> *) where
  starN :: ent True (S' (S' n))
  inhabit :: ent True (S' l) ->  (ent True l -> ent o l') -> ent False l'
  isle :: ent o l -> ent False (S' l)
  descope :: ent o l -> ent False l

class Inhabitable ent => LC (ent :: Bool -> Nat' -> *) where
  lam :: (ent False l -> ent False l) -> ent False l
  (&) :: ent o l -> ent p l -> ent False l

-- #### Implement these in terms of the Lambda-Pi calculus
--
data Lam open lev where
  App :: Lam o l -> Lam p l -> Lam False l
  Inh :: Lam True (S' l) ->  (Lam True l -> Lam o l') -> Lam False l'
  Star :: Lam True (S' (S' n))
  Close :: Lam True l -> Lam False l
  Habitant :: Lam True (S' l) -> Lam True l -- needed for concretising
  Lam :: (Lam False l -> Lam False l) -> Lam False l
  Pi :: (Lam False l -> Lam False (S' l)) -> Lam False (S' l)

instance Show (Lam o l) where
  show Star = "*"
  show (Close a) = '[' : (show a ++ "]")
  show (Habitant a) = "habitant of " ++ show a
  show (Inh isle f) = "Below " ++ show isle ++ " is a " ++ show (f (Habitant isle)) 
  show (f `App` a) = "(" ++ show f ++ " & " ++show a ++ ")" 
  show (Lam f) = "(\\" ++ show inp ++ " . " ++ show (f inp) ++ ")"
    where inp = Close (Habitant $ Habitant Star) -- FIXME

instance Inhabitable Lam where
  starN = Star
  inhabit = Inh
  isle Star = Close Star
  isle (Close a) = isle a
  isle (Habitant a) = Close a
  isle (Lam f) = Pi $ isle . f
  isle (Pi f) = Close Star
  descope (Inh isle f) = descope $ f $ Habitant isle
  descope (f `App` a) = descope f `App` descope a
  descope cs@Close{} = cs
  descope ho@Habitant{} = Close ho
  descope (Lam f) = Lam $ \x -> descope $ f x -- inefficient!
  descope whatever = error $ " ##### how to descope this:   ### " ++ show whatever

star :: Inhabitable ent => ent True (S' (S' Z'))
star = starN



(>>=) :: Inhabitable ent => ent True (S' l) -> (ent True l -> ent o l') -> ent False l'
(>>=) = inhabit

instance LC Lam where
  lam = Lam
  (&) = App


--return :: Inhabitable ent => ent o l -> ent False l
return = undefined
fail = error

knoth :: LC ent => ent False Z'
knoth = do int <- star
           i <- int
           j <- int
           -- k <- int & int -- Error: not open, good
           -- sub <- i       -- Error: cannot descend below zero, good
           i & j


regain :: Inhabitable ent => ent False (S' Z')
regain = descope $ do
            int <- star
            i <- int
            isle i

func' :: LC ent => ent False Z'
func' = do int <- star
           i <- int
           j <- int
           let k = lam (\c -> lam (const c))
           k & i & j

func :: LC ent => ent False Z'
func = descope func'
