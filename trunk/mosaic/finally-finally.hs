{-# LANGUAGE ConstraintKinds, DataKinds, PolyKinds, RankNTypes, ImpredicativeTypes, TypeFamilies
           , MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

-- To have lenses etc. for finally-tagless form we need a
-- way to create custom class dictionaries (and possibly
-- abuse reflection to create them on the fly). But why
-- not create a concept of final dictionaries, where we
-- are not restricted to the concept of finally-tagless
-- to be implemented by Haskell type classes?

class Foo' a where
  bar :: Char -> Bool -> a
  quux :: a -> a -> a



class Dict (d :: [*] -> k) (ms :: [*]) where
  type First d ms :: *
  first :: First d ms

--type F = Functor
-- ERROR?! type Foo = forall a . Foo' a => '[Char -> Bool -> a, a -> a -> a]
--type Foo = '[forall a . Foo' a => Char -> Bool -> a, forall a . Foo' a => a -> a -> a]
type Foo a = '[Char -> Bool -> a, a -> a -> a]


data F (vs :: [*]) = Bar Char Bool | Quux (F vs) (F vs)
class G (vs :: [*]) where

instance Dict F (Foo (F a)) where
  --type First F Foo = forall a . Foo' a => Char -> Bool -> a
  type First F (Foo (F a)) = Char -> Bool -> F a
  first = Bar

--instance Dict G (Foo (G a)) where