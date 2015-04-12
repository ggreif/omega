{-# LANGUAGE ConstraintKinds, GADTs, TypeFamilies, PolyKinds, KindSignatures
           , TypeOperators, DataKinds #-}

import Data.Proxy
import GHC.Exts

type family Elem (t :: k) (ts :: [k]) :: Bool where
  Elem a '[] = False
  Elem a (a ': as) = True
  Elem a (b ': bs) = Elem a bs

type family ElemOf (t :: k) (ts :: [k]) :: Constraint where
  ElemOf a (a ': as) = ()
  ElemOf a (b ': bs) = ElemOf a bs


class Known (v :: k)

data Term :: [k] -> * where
  -- operator symbols
  Arr :: Term vs -> Term vs -> Term vs
  V :: (Known v, v `ElemOf` vs) => Proxy v -> Term vs
