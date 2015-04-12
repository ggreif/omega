{-# LANGUAGE ConstraintKinds, GADTs, TypeFamilies, PolyKinds, KindSignatures
           , TypeOperators, DataKinds, FlexibleInstances, UndecidableInstances
           , StandaloneDeriving #-}

import Data.Proxy
import GHC.Exts
import GHC.TypeLits

type family Elem (t :: k) (ts :: [k]) :: Bool where
  Elem a '[] = False
  Elem a (a ': as) = True
  Elem a (b ': bs) = Elem a bs

type family ElemOf (t :: k) (ts :: [k]) :: Constraint where
  ElemOf a (a ': as) = ()
  ElemOf a (b ': bs) = ElemOf a bs


class Known (v :: k) where
  --order
instance KnownSymbol s => Known s where
  --order = undefined
instance KnownNat n => Known n where

data Term :: [k] -> * where
  -- operator symbols
  Arr :: Term vs -> Term vs -> Term vs
  V :: (Known v, v `ElemOf` vs) => Proxy v -> Term vs

deriving instance Show (Term vs)
