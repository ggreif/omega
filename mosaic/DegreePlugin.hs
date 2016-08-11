{-# LANGUAGE DataKinds, KindSignatures, PolyKinds, TypeFamilies, TypeOperators, ViewPatterns, TemplateHaskell, RankNTypes #-}

import GHC.Exts
import Language.Haskell.TH

data family (refin :: k) ° typ
infix 1 °

newtype instance Just a ° Maybe b = ΘJust (Maybe b)
newtype instance Nothing ° Maybe b = ΘNothing (Maybe b)

newtype instance True ° Bool = ΘTrue Bool
newtype instance False ° Bool = ΘFalse Bool


test :: Just a ° Maybe b -> b
test (coerce -> Just a) = a

type family (l :: k) ¦ (r :: k) :: k where { a ¦ b = a } -- can be empty in 8.0
infixl 2 ¦

t1 =
 [d|
 test1 :: Just a ° Maybe b -> a ° b
 test2 :: Just a ¦ Nothing ° Maybe b -> Maybe (a ° b)
 test1 (Just a) = a -- WE WANT HERE
 test2 (Just a) = Just a -- WE WANT HERE
 test2 Nothing = Nothing -- WE WANT HERE
 test3 :: forall a b . Just a ° Maybe b -> a ° b -- hint that /a/ comes from outside (i.e. not an existential/pi type)
 test3 (Just a) = a -- WE WANT HERE
 test4 :: Just a ° Maybe b -> Maybe b -- /a/ is considered to be existentially bound by a pi
  |]
-- HINT: runQ t1 >>= print


-- Plugin's job: test_aww :: Just a ° Maybe Bool -> a ° Bool
test_aww :: Just True ° Maybe Bool -> True ° Bool
test_aww (ΘJust (Just a)) = coerce a
--test_aww (coerce -> (Just a)) = coerce a -- BUG?? Couldn't match representation of type ‘a0’ with that of ‘Bool’


-- PLAN: can we outsource the type checking of this to a plugin
--       in the style of http://adam.gundry.co.uk/pub/typechecker-plugins/

-- (°) must be injective in the second arg
-- implement the right refinement semantics

-- Can a plugin see
--      test_aww (Just a) = a
-- at all?
-- Or do we need Template haskell for that to massage it first?

-- * Todos

-- - add a Servant-style typeclass (fundep?) to create (pattern-matching?) wrapper
--   around a degree-typed function, eliminating the degrees in the process.
-- - in TH consider universally qualified tyvars coming from a degree as
--   /scope-extended/ tyvars (a.k.a. pi-binders)

