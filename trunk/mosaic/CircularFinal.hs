{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, UndecidableInstances
           , FlexibleInstances, FunctionalDependencies #-}
import Prelude hiding (max)

-- see: Axelsson, Klaessen: Using Circular Programs for Higher-Order Syntax
-- ICFP 2013

class LC p where
  app :: p -> p -> p
  lam :: (p -> p) -> p


-- first order interpretation

data Lam name = Var name | App (Lam name) (Lam name) | Lam name (Lam name)

-- join monoid

--class LC (p t) => Join p t | p -> t where
--class LC (lc t) => Join lc t where
class Join t where
  bot :: t
  prime :: t -> t
  (|-|) :: t -> t -> t
  --max :: lc t -> t
  max :: LC (lc t) => lc t -> t

--instance Join (Lam name) name => LC (Lam name) where
--instance Join Lam name => LC (Lam name) where
instance Join name => LC (Lam name) where
  app = App
  lam f = Lam name body
    where body = f (Var name)
          name = prime (max body)

--instance Join (Lam name) name
--instance Join Lam name
instance Join name
