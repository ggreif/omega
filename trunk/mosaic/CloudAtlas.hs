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

type family AlienTo (t :: k) (ts :: [k]) :: Constraint where
  AlienTo a '[] = ()
  AlienTo a (a ': as) = True ~ False
  AlienTo a (b ': bs) = AlienTo a bs


instance {-# OVERLAPPING #-} KnownSymbol s => Show (Proxy (s :: Symbol)) where
  show = ('#' :) . symbolVal
instance {-# OVERLAPPING #-} KnownNat n => Show (Proxy (n :: Nat)) where
  show = ('#' :) . show . natVal


type family MoreKnown (v :: k) :: Constraint where
  MoreKnown (s :: Symbol) = KnownSymbol s
  MoreKnown (n :: Nat) = KnownNat n

class MoreKnown v => Known (v :: k) where
  --order
instance KnownSymbol s => Known s where
  --order = undefined
instance KnownNat n => Known n where

data Term :: [k] -> * where
  -- operator symbols
  Arr :: Term vs -> Term vs -> Term vs
  V :: (Known v, v `ElemOf` vs) => Proxy v -> Term vs

deriving instance {-# OVERLAPPING #-} Show (Term (vs :: [Nat]))
deriving instance {-# OVERLAPPING #-} Show (Term (vs :: [Symbol]))
deriving instance Show (Term vs) -- BUG?? does not pick up orphans


data Subst :: [k] -> [j] -> * where
  Empty :: Subst '[] vs
  Extend :: (Known b, b `AlienTo` bs) => Proxy b -> Term tv -> bs `Subst` tv -> (b ': bs) `Subst` tv

deriving instance {-# OVERLAPPING #-} Show (Subst (bvs :: [Symbol]) (tvs :: [Symbol]))
deriving instance {-# OVERLAPPING #-} Show (Subst (bvs :: [Nat]) (tvs :: [Symbol]))
deriving instance {-# OVERLAPPING #-} Show (Subst (bvs :: [Symbol]) (tvs :: [Nat]))
deriving instance {-# OVERLAPPING #-} Show (Subst (bvs :: [Nat]) (tvs :: [Nat]))
deriving instance Show (Subst bvs tvs)

t0 = V (Proxy :: Proxy "a") :: Term '["a", "b"]
t1 = V (Proxy :: Proxy "b") :: Term '["a", "b"]
t2 = Extend (Proxy :: Proxy 0) t1 Empty
t3 = Extend (Proxy :: Proxy 0) t0 (Extend (Proxy :: Proxy 1) t1 Empty)
