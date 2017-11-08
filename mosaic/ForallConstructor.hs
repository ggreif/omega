{-# language ScopedTypeVariables, DataKinds, RankNTypes, TypeOperators, TypeFamilies, TypeInType #-}

import Data.Kind

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

class Univ u where
  constr :: (forall t . u f (t:ctx)) -> u f ctx
  use :: u (Just t) (t:ctx)
  up :: u (Just t) (t:ctx) -> u (Just t) (s:t:ctx)
  star'arr :: (forall star arr . u Nothing '[arr, star]) -> u Nothing '[]
  gather :: u (Just t) ctx -> u Nothing '[t] -> u f ctx
  gather2 :: u (Just t) ctx -> u (Just t) ctx -> u Nothing '[t] -> u f ctx

t1,t2 :: forall u . Univ u => u Nothing '[]
--t1 = star'arr $ constr (constr $ up $ up $ up (use :: u (Just _) _))
t1 = star'arr $ constr (constr $ gather (up $ up $ up use) (undefined {-:: u Nothing _-}))
t2 = star'arr $ constr (constr $ gather2 (up $ up $ up use) (up $ up $ up use) (undefined))

--sameness :: a -> a 
