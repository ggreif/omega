{-# LANGUAGE DataKinds, KindSignatures, PolyKinds, TypeFamilies, TypeOperators, ViewPatterns, TemplateHaskell #-}

import GHC.Exts

--type family (refin :: k) ° typ
--data (refin :: k) ° typ
--newtype (refin :: k) ° typ = Refined typ
data family (refin :: k) ° typ

newtype instance (Just a ° Maybe b) = RefinedJust (Maybe b)
newtype instance (Nothing ° Maybe b) = RefinedNothing (Maybe b)

newtype instance (True ° Bool) = RefinedTrue Bool
newtype instance (False ° Bool) = RefinedFalse Bool


test :: (Just a ° Maybe b) -> b
test (coerce -> (Just a)) = a

[d|
 test1 :: (Just a ° Maybe b) -> b
 -- test1 (Just a) = a -- WE WANT HERE
 test1 (RefinedJust (Just a)) = a
  |]

-- Plugin's job: test_aww :: (Just a ° Maybe Bool) -> a ° Bool
test_aww :: (Just True ° Maybe Bool) -> True ° Bool
test_aww (RefinedJust (Just a)) = coerce a
--test_aww (coerce -> (Just a)) = coerce a -- BUG?? Couldn't match representation of type ‘a0’ with that of ‘Bool’


-- PLAN: can we outsource the type checking of this to a plugin
--       in the style of http://adam.gundry.co.uk/pub/typechecker-plugins/

-- (°) must be injective in the second arg
-- implement the right refinement semantics

-- Can a plugin see
--      test_aww (Just a) = a
-- at all?
-- Or do we need Template haskell for that to massage it first?
