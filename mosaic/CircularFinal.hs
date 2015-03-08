{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
import Prelude hiding (max)
import qualified Prelude as Prelude (max)

-- see: Axelsson, Klaessen: Using Circular Programs for Higher-Order Syntax
-- ICFP 2013

class LC p where
  app :: p -> p -> p
  lam :: (p -> p) -> p


-- first order interpretation

data Lam name = Var name
              | App (Lam name) (Lam name)
              | Lam name (Lam name)
              | Lam name `Cho` Lam name
  deriving Show

-- join monoid

class Join t where
  bot :: t
  prime :: t -> t
  (|-|) :: t -> t -> t

class Max lc t where
  max :: lc t -> t

instance Join name => LC (Lam name) where
  app = App
  lam f = Lam name body
    where body = f (Var name)
          name = prime (max body)

-- operator for indeterministic choice

class LC p => Indet p where
  (~~) :: p -> p -> p


instance Join Int where
  bot = 0
  prime = (+1)
  (|-|) = Prelude.max

instance Join name => Max Lam name where
  max (Var _) = bot
  max (f `App` a) = max f |-| max a
  max (a `Cho` b) = max a |-| max b
  max (Lam name _) = name


t1' :: LC p => p
t1' = lam (\a -> a `app` a)

t1 :: Lam Int
t1 = t1'

t2' :: LC p => p
t2' = lam (\a -> lam (\b -> a `app` b))

t2 :: Lam Int
t2 = t2'

t3' :: Indet p => p
t3' = lam (\a -> lam (\b -> a ~~ b))

--t3 :: Lam (Int, Int)
t3 :: (Lam Int, Lam Int)
t3 = t3'

t0' :: Indet p => p
t0' = lam (\a -> a ~~ a)

t0 :: (Lam Int, Ty)
t0 = t0'


-- ########### the pairing trick ###########

instance (LC r, LC r') => LC (r, r') where
  (f, f') `app` (a, a') = (f `app` a, f' `app` a')
  lam f = (lam f1, lam f2)
      where f1 a = fst $ f (a, undefined) -- provide a bottom
            f2 a' = snd $ f (undefined, a') -- provide a bottom

instance (Indet p, Indet p') => Indet (p, p') where
  (l, l') ~~ (r, r') = (l ~~ r, l' ~~ r')

-- ########### can we use a similar trick for type inference? ###########

instance Join name => Indet (Lam name) where
  (~~) = Cho

{-
instance Join name => Join (name, Int) where
  bot = (bot, 42)
  prime (p, x) = (prime p, x)
  (a, x) |-| (b, y) = (a |-| b, x)
-}

-- develop a vocabulary for inference
--class LC (Lam name) => Inf p name where
--  ofvar :: name -> p -- type of variable named
class LC p => Inf p where
  ofvar :: p -> p -- type of variable (must be variable!)
  equate :: p -> p -> p
  arr :: p -> p -> p

newtype Up a = Up a -- e.g. a LC one level up (vals -> tys)

instance LC p => LC (Up p) where
  Up f `app` Up a = Up $ undefined -- plan: intro an abstraction arrow and apply it on type of arg to obtain type of result


data Ty = Univ Int | Ty `Equate` Ty | Ty `Arr` Ty | Ty `TApp` Ty | Fresh
  deriving Show

instance LC Ty where
  f `app` a = (f `Equate` (a `Arr` Fresh)) `TApp` a
  lam f = u `Arr` f u
    where u = Univ 0

instance Indet Ty where
  (~~) = Equate