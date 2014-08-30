{-# LANGUAGE ConstraintKinds, DataKinds, PolyKinds, RankNTypes, ImpredicativeTypes #-}

-- To have lenses etc. for finally-tagless form we need a
-- way to create custom class dictionaries (and possibly
-- abuse reflection to create them on the fly). But why
-- not create a concept of final dictionaries, where we
-- are not restricted to the concept of finally-tagless
-- to be implemented by Haskell type classes?

class Foo' a where
  bar :: Char -> Bool -> a
  quux :: a -> a -> a

class Dict (d :: [*] -> k) where

--type F = Functor
-- ERROR?! type Foo = forall a . Foo' a => '[Char -> Bool -> a, a -> a -> a]
type Foo = '[forall a . Foo' a => Char -> Bool -> a, forall a . Foo' a => a -> a -> a]


data F (vs :: [*]) = XX
class G (vs :: [*]) where

instance Dict F where
instance Dict G where