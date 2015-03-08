{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
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

--instance Join name => LC (Lam (name, Int)) where
instance LC (Lam (Int, Lam Int)) where
  app = App
  lam f = Lam name body
    where body = f (Var name)
          name = prime (max body)

instance Join Int where
  bot = 0
  prime = (+1)
  (|-|) = Prelude.max

t1' :: LC p => p
t1' = lam (\a -> a `app` a)

--t1 :: Lam Int
--t1 = t1'

t2' :: LC p => p
t2' = lam (\a -> lam (\b -> a `app` b))

--t2 :: Lam Int
--t2 = t2'

t3' :: Indet p => p
t3' = lam (\a -> lam (\b -> a ~~ b))

t3 :: Lam (Int, Lam Int)
t3 = t3'

-- ########### can we use a similar trick for type inference? ###########

-- operator for indeterministic choice

class LC p => Indet p where
  (~~) :: p -> p -> p


--instance Join name => Indet (Lam (name, Int)) where
instance Indet (Lam (Int, Lam Int)) where
  (~~) = Cho

instance Join name => Join (name, Lam Int) where
  bot = (bot, Var 42)
  prime (p, x) = (prime p, x)
  (a, x) |-| (b, y) = (a |-| b, x)

--instance (name ~ Int, Join name) => Max Lam (name, Int) where
instance Max Lam (Int, Lam Int) where
  max v@(Var n) = (bot, Var $ fst n)
  max (f `App` a) = (fst (max f) |-| fst (max a), Var 88)
  max (a `Cho` b) = (fst ma |-| fst mb, snd ma `uni` snd mb)
    where ma = max a
          mb = max b
          uni :: Lam Int -> Lam Int -> Lam Int
          Var l `uni` Var r = Var $ l `Prelude.max` r
  max (Lam (name, ty) _) = (name, ty)

