{-# LANGUAGE DataKinds, KindSignatures, PolyKinds, TypeFamilies, TypeOperators #-}

--type family (refin :: k) ° typ
--data (refin :: k) ° typ
--newtype (refin :: k) ° typ = Refined typ
data family (refin :: k) ° typ --  = Refined typ

newtype instance (Just a ° Maybe b) = RefinedJust (Maybe b)
newtype instance (Nothing ° Maybe b) = RefinedNothing (Maybe b)

test :: (Just a ° Maybe b) -> b
test (RefinedJust (Just a)) = a

test_aww :: (Just a ° Maybe b) -> (a ° b)
test_aww (RefinedJust (Just a)) = undefined -- a


-- PLAN: can we outsource the type checking of this to a plugin
--       in the style of http://adam.gundry.co.uk/pub/typechecker-plugins/

-- () must be injective in the second arg
-- implement the right refinement semantics

-- Can a plugin see
--      test_aww (Just a) = a
-- at all?
-- Or do we need Template haskell for that to massage it first?
