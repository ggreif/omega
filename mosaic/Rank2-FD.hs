{-# LANGUAGE FunctionalDependencies, RankNTypes, GADTs, FlexibleContexts, UndecidableInstances, PolyKinds #-}

-- THIS FILE IS JUST FOR HUNTING
--  DOWN A PROBLEM experienced in AddType.hs
--  when that is solved, this can be deleted

import Data.Proxy

data Bar where
  B0 :: Proxy f'{-unneeded-} -> (forall a . Integral a => f a) -> (forall a . (Integral a, Hyp (f a) b) => f a -> b) -> Bar



class Foo a b | a -> b where
  foo :: a -> b

class Hyp a b | a -> b

instance (Integral a, Hyp (Maybe a) Integer) => Foo (Maybe a) Integer where
  foo Nothing = 0
  foo (Just a) = toInteger a


supplyHyp :: (forall a . (Integral a, Hyp (f a) b) => ((f a) -> b, f a)) -> Int
supplyHyp = undefined

instance Foo Bar Int where
  foo (B0 Proxy d fo) = supplyHyp (fo, d)

t1 = B0 (Proxy :: Proxy Maybe) (Just 42) foo
