{-# language DataKinds, RankNTypes, TypeOperators, TypeInType #-}


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

-- ** Task
-- define in Univ something like
--     data Foo
--     data Bar

class Univ u where
  constr :: (forall t . u (t:ctx)) -> u ctx
  use :: u (t:ctx)

t1 :: Univ u => u '[]
t1 = constr (constr use)
