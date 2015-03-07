{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
import Prelude hiding (max)
import qualified Prelude as Prelude (max)

-- see: Axelsson, Klaessen: Using Circular Programs for Higher-Order Syntax
-- ICFP 2013

class LC p where
  app :: p -> p -> p
  lam :: (p -> p) -> p


-- first order interpretation

data Lam name = Var name | App (Lam name) (Lam name) | Lam name (Lam name)
  deriving Show

-- join monoid

class Join t where
  bot :: t
  prime :: t -> t
  (|-|) :: t -> t -> t

class (Join t, LC (lc t)) => Max lc t where
  max :: lc t -> t

instance Join name => LC (Lam name) where
  app = App
  lam f = Lam name body
    where body = f (Var name)
          name = prime (max body)

instance Join Int where
  bot = 0
  prime = (+1)
  (|-|) = Prelude.max

instance Join name => Max Lam name where
  max (Var _) = bot
  max (f `App` a) = max f |-| max a
  max (Lam name _) = name


t1' :: LC p => p
t1' = lam (\a -> a `app` a)

t1 :: Lam Int
t1 = t1'

t2' :: LC p => p
t2' = lam (\a -> lam (\b -> a `app` b))

t2 :: Lam Int
t2 = t2'