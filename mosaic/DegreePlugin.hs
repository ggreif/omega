{-# LANGUAGE DataKinds, KindSignatures, PolyKinds, TypeFamilies, TypeOperators #-}

--type family (refin :: k) ° typ
data (refin :: k) ° typ

test :: (Just a ° Maybe b) -> b
test (Just a) = a

test_aww :: (Just a ° Maybe b) -> (a ° b)
test_aww (Just a) = a


-- PLAN: can we outsource the type checking of this to a plugin
--       in the style of http://adam.gundry.co.uk/pub/typechecker-plugins/

-- (°) must be injective in the second arg
-- implement the right refinement semantics

-- Can a plugin see
--      test_aww (Just a) = a
-- at all?
-- Or do we need Template haskell for that to massage it first?
