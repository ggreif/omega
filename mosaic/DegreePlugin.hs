{-# LANGUAGE DataKinds, KindSignatures, PolyKinds, TypeFamilies, TypeOperators, ViewPatterns, TemplateHaskell #-}

import GHC.Exts
import Language.Haskell.TH

data family (refin :: k) ° typ

newtype instance (Just a ° Maybe b) = ΘJust (Maybe b)
newtype instance (Nothing ° Maybe b) = ΘNothing (Maybe b)

newtype instance (True ° Bool) = ΘTrue Bool
newtype instance (False ° Bool) = ΘFalse Bool


test :: (Just a ° Maybe b) -> b
test (coerce -> (Just a)) = a

t1 =
 [d|
 test1 :: (Just a ° Maybe b) -> a ° b
 test1 (Just a) = a -- WE WANT HERE
  |]
-- HINT: runQ t1 >>= print


-- Plugin's job: test_aww :: (Just a ° Maybe Bool) -> a ° Bool
test_aww :: (Just True ° Maybe Bool) -> True ° Bool
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
