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

t3'' :: (Ty Int, Ty Int, [Ty Int])
t3'' = t3'

t3''' :: Ty Int
t3''' = t3'


t0' :: Indet p => p
t0' = lam (\a -> a ~~ a)

t0 :: (Lam Int, Ty Int)
t0 = t0'

t5' :: Indet p => p
t5' = lam (\a -> lam (\b -> b ~~ b) `app` a)

t5 :: (Lam Int, Ty Int)
t5 = t5'

t6' :: LC p => p
t6' = lam (\a -> a)

t6 :: (Ty Int, Ty Int, [Ty Int])
t6 = t6'


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


data Ty name = Univ name | Ty name `Equate` Ty name | Ty name `Arr` Ty name | Ty name `TApp` Ty name | Fresh
  deriving Show

instance Join name => Max Ty name where
  max Fresh = bot
  max (Univ _) = bot
  max (f `TApp` a) = max f |-| max a
  max (a `Equate` b) = max a |-| max b
  --max (Lam name _) = name
  max (a `Arr` b) = max a |-| max b


instance Join name => LC (Ty name) where
  f `app` a = (f `Equate` (a `Arr` Fresh)) `TApp` a
  lam f = u `Arr` body
    where u = Univ name
          body = f u
          name = prime (max body)

instance Join name => Indet (Ty name) where
  (~~) = Equate


data AllEquates = AE (Ty Int) ((Int, [Ty Int]) -> (Int, [Ty Int]))

-- ##### experiment with collecting equate constraints
instance Indet (Ty Int, Ty Int, [Ty Int]) where
  (lty, Univ l, ls) ~~ (rty, Univ r, rs) | l == r = (lty ~~ rty, Univ l, ls ++ rs)
  (lty, Univ l, ls) ~~ (rty, Univ r, rs) | l > r = (lty ~~ rty, Univ l, Univ r : ls)
  (lty, Univ l, ls) ~~ (rty, Univ r, rs) | l < r = (lty ~~ rty, Univ r, Univ l : rs)

instance LC (Ty Int, Ty Int, [Ty Int]) where
  lam f = f (arrow, u, [])
    where f1 a = fst (f (a, Univ bot, []))
          fst (a, b, c) = a
          arrow@(u@Univ{} `Arr` _) = lam f1


-- ##### have a type-level fixpoint, eliminating equated universals.
