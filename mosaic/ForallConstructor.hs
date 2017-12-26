{-# language ScopedTypeVariables, DataKinds, GADTs, RankNTypes, TypeOperators, TypeFamilies, TypeInType, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts #-}

import Data.Kind
import Data.Proxy
import Data.Reflection

-- * Idea
-- Every rank-N forall gives rise to a type that only unifies with itself
-- A value which has that type thus cannot be passed anywhere else.
-- This pretty much parallels the definition of data/type constructors.
-- So instead of having productions for defining constructors, why not
-- only have those foralls and /consider/ them being constructors.

-- ** Simplifying assumptions
-- - Disregard levels for now
-- - let's have one (open) kind and create type constructors
-- - only have linear places (hrm, no places at all in the beginning)
-- - places follow cons, not snoc order

-- ** Task
-- define in Univ something like
--     data Foo
--     data Bar
--     fb :: Foo -> Bar
--     data Quux a
--     Refl :: a :~: a

-- ** Open problems
-- - express =data Foo :: *=, i.e. inhabitance
-- - express that /star/ is nullary
-- - express that =(->)= is binary
-- - check sameness of foci

-- ** Modelling arities
-- have a snoc list with existentials

data C where
  N :: C
  (:.) :: C -> a -> C

infixl 5 :.

class UnivX u where
  star'arrX :: (forall (star :: ()) (arr :: Below star -> Below star -> Below star) . u (N :. star :. arr)) -> u N

-- ** Modelling pattern matching
-- something like data Peano = Z | S Peano
-- and plus Z n = n; plus (S m) n = S (plus m n)


-- ** Modelling inhabitation
-- we want something like (0: Just 'l', 1: Maybe Char, 2: *)
-- which we could type as '[(0, App just ell), (1, App maybe char), (2, star)]
-- or possibly '[App just ell, App maybe char, star 2]
-- anyway sticking an inhabitant under a RankN-bound name is tricky
-- Plan a)
-- can we use a constraint and say (forall just . TypeOf just ~ '[(->) `App` fresh `App` (maybe `App` fresh), star 2])
-- Plan b)
-- employ TypeInType and ornament the kind
-- (forall just :: With '[(->) `App` fresh `App` (maybe `App` fresh), star 2]).

foo :: b -> (forall a. a ~ [b] => a -> b) -> b
foo b f = f $ pure b
bar = foo 'a' head

data Below t

planb :: (forall a. forall (b :: Below a) . forall (c :: Below b) . a -> (Proxy c, Tower c))
planb = \_ -> (Proxy, [[()]])

class Strata a where
  type Tower a :: *

instance Strata (a :: *) where
  type Tower a = ()
instance Strata b => Strata (a :: Below b) where
  type Tower (a :: Below b) = [Tower b]

class Univ u where
  constr :: (forall t . u f (t:ctx)) -> u f ctx
  use :: u (Just t) (t:ctx)
  up :: u (Just f) ctx -> u (Just f) (s:ctx)
  star'arr :: (forall star arr . u Nothing '[arr, star]) -> u Nothing '[]
  --star'arrX :: (forall (star :: ()) arr . u Nothing '[arr, star]) -> u Nothing '[]
  gather :: u (Just t) ctx -> u Nothing '[t] -> u f ctx
  gather2 :: u (Just t) ctx -> u (Just t) ctx -> u Nothing '[t] -> u f ctx

t1,t2 :: forall u . Univ u => u Nothing '[]
--t1 = star'arr $ constr (constr $ up $ up $ up (use :: u (Just _) _))
t1 = star'arr $ constr (constr $ gather (up $ up $ up use) (undefined {-:: u Nothing _-}))
t2 = star'arr $ constr (constr $ gather2 (up $ up $ up use) (up $ up $ up use) (undefined))

--sameness :: a -> a 


-- * Can we have a mapping form a Loc to a rank-2 type?

-- say, Loc is the Bool kind, can True map to one forall and False to the other?

data Expr a

class Localised (l :: Bool) a | l -> a, a -> l where


lam :: (forall a . Localised True a => Expr a) -> Expr Int
lam e = undefined

-- can we use reflection to create instance on the fly?
-- http://www.tweag.io/posts/2017-12-21-reflection-tutorial.html

fortyTwo = reifyMonoid (+) (-2) (foldMap ReflectedMonoid) [2,3,4,5,6,7,8,9]
