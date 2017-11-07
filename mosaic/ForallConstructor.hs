{-# language DataKinds, RankNTypes, TypeOperators, TypeFamilies, TypeInType #-}

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

class u ~ v t => Univ u where
  --type Focus u f (ctx :: [*]) -- :: f -> u ctx
  constr :: (forall t . u (t:ctx)) -> u ctx
  --use :: Focus u t (t:ctx)
  use :: u (t:ctx)
  up :: u (t:ctx) -> u (s:t:ctx)
  star'arr :: (forall star arr . u '[arr, star]) -> u '[]

t1 :: Univ u => u '[]
t1 = constr (constr $ up use)

--sameness :: a -> a 
