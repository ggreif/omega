{-# LANGUAGE FunctionalDependencies, RankNTypes, GADTs, FlexibleContexts, UndecidableInstances, PolyKinds, FlexibleInstances #-}

-- THIS FILE IS JUST FOR HUNTING
--  DOWN A PROBLEM experienced in AddType.hs
--  when that is solved, this can be deleted

import Data.Proxy

data Bar where
  B0 :: (forall a . Integral a => f a) -> (forall a b . (Integral a, Hyp (f a) b) => f a -> b) -> Bar
  B0' :: (forall a . Integral a => f a) -> (forall a . (Integral a, Hyp (f a) a) => f a -> a) -> Bar
  B0'' :: (forall a . Integral a => f a) -> (forall a . (Hyp (f Integer) Integer) => f Integer -> Integer) -> Bar
  B1 :: (forall a . Integral a => f a) -> (forall a b . (Foo (f a) b) => f a -> b) -> Bar


class Foo a b | a -> b where
  foo :: a -> b

class Hyp a b | a -> b

instance (Integral a, Hyp (Maybe a) a) => Foo (Maybe a) a where
  foo Nothing = 0
  foo (Just a) = a

instance Hyp [Integer] Integer => Foo [Integer] Integer where
  foo [] = 0
  foo [a] = a


supplyHyp :: Integral a => (Hyp (f a) b => (f a -> b, f a)) -> b
supplyHyp = undefined

instance Foo Bar Int where
  foo (B0 d fo) = supplyHyp (fo, d)
  foo (B0' d fo) = supplyHyp (fo, d)
  foo (B0'' d fo) = fromIntegral (supplyHyp (fo, d))

--t0 = B0 (Just 42) foo -- I want this
t0' = B0' (Just 42) foo
--t0l = B0 ([42]) foo -- and this
t0'' = B0'' ([42]) foo
t1m = B1 (Just 42) foo
t1 = B1 [42] foo
