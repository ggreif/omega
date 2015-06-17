{-# LANGUAGE ConstraintKinds, GADTs, TypeFamilies, PolyKinds, KindSignatures
           , TypeOperators, DataKinds, FlexibleInstances, UndecidableInstances
           , StandaloneDeriving, MultiParamTypeClasses #-}

import Data.Proxy
import Data.Type.Equality
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

class ApartFrom (t :: k) (ts :: [k])
instance AlienTo t ts => ApartFrom t ts

instance ApartFrom (ts :: [k]) ('[] :: [[k]])
instance ((ts `Intersect` us) ~ '[]) => ApartFrom (ts :: [k]) ((us ': uss) :: [[k]])

type family Intersect (ts :: [k]) (us :: [k]) :: [k] where
  Intersect '[] r = '[]
  Intersect l '[] = '[]
  Intersect (l ': ls) r = InterAppend (Intersect ls r) r l

-- helper
type family InterAppend (l :: [k]) (r :: [k]) (one :: k) :: [k] where
  InterAppend acc '[] one = acc
  InterAppend acc (one ': rs) one = one ': acc
  InterAppend acc (r ': rs) one = InterAppend acc rs one


instance {-# OVERLAPPING #-} KnownSymbol s => Show (Proxy (s :: Symbol)) where
  show = ('#' :) . symbolVal
instance {-# OVERLAPPING #-} KnownNat n => Show (Proxy (n :: Nat)) where
  show = ('#' :) . show . natVal


type family MoreKnown (v :: k) :: Constraint where
  MoreKnown (s :: Symbol) = KnownSymbol s
  MoreKnown (n :: Nat) = KnownNat n
  MoreKnown (ss :: [Symbol]) = KnownSymbols ss
  MoreKnown (ns :: [Nat]) = KnownNats ns

class MoreKnown v => Known (v :: k) where
  same :: Known (v' :: k) => Proxy v -> Proxy v' -> Maybe (v :~: v')
  --order
instance KnownSymbol s => Known s where
  same = sameSymbol
  --order = undefined
instance KnownNat n => Known n where
  same = sameNat

instance KnownNats ns => Known (ns :: [Nat]) where
instance KnownSymbols ss => Known (ss :: [Symbol]) where

class ListOf (test :: k -> Constraint) (ks :: [k])

instance ListOf test '[]
instance (test k, ListOf test ks) => ListOf test (k ': ks)

type KnownSymbols = ListOf KnownSymbol
type KnownNats = ListOf KnownNat

data Term :: [k] -> * where
  -- operator symbols
  Arr :: Term vs -> Term vs -> Term vs
  Int :: Term vs
  -- PHOAS variable
  V :: (Known v, v `ElemOf` vs) => Proxy v -> Term vs

deriving instance {-# OVERLAPPING #-} Show (Term (vs :: [Nat]))
deriving instance {-# OVERLAPPING #-} Show (Term (vs :: [Symbol]))
deriving instance Show (Term vs) -- BUG?? does not pick up orphans


data Subst :: [k] -> [j] -> * where
  Empty :: Subst '[] vs
  Extend :: (Known b, b `ApartFrom` bs) => Proxy b -> Term tv -> bs `Subst` tv -> (b ': bs) `Subst` tv

deriving instance {-# OVERLAPPING #-} Show (Subst (bvs :: [Symbol]) (tvs :: [Symbol]))
deriving instance {-# OVERLAPPING #-} Show (Subst (bvs :: [Nat]) (tvs :: [Symbol]))
deriving instance {-# OVERLAPPING #-} Show (Subst (bvs :: [Symbol]) (tvs :: [Nat]))
deriving instance {-# OVERLAPPING #-} Show (Subst (bvs :: [Nat]) (tvs :: [Nat]))
deriving instance Show (Subst bvs tvs)

t0 = V (Proxy :: Proxy "a") :: Term '["a", "b"]
t1 = V (Proxy :: Proxy "b") :: Term '["a", "b"]
t2 = Extend (Proxy :: Proxy 0) t0 Empty
t3 = Extend (Proxy :: Proxy 1) t1 t2
t4 = Extend (Proxy :: Proxy 2) Int t3
t5 = Extend (Proxy :: Proxy 3) (Arr Int t1) t4

t10 = V (Proxy :: Proxy '["a"]) :: Term '[ '["a"], '["b"] ]

s :: Term ks -> ks `Subst` js -> Term js
v@V{} `s` subst = v `search` subst
  where search :: Term (ks :: [k]) -> (ks' :: [k]) `Subst` js -> Term js
        V p `search` (Extend p' t rest) | Just Refl <- p `same` p' = t
        v@V{} `search` (Extend _ _ rest) = v `search` rest
Int `s` _ = Int
Arr d c `s` subst = Arr (d `s` subst) (c `s` subst)

t11 = V (Proxy :: Proxy "a") `s` Extend (Proxy :: Proxy "b") Int (Extend (Proxy :: Proxy "a") (Int `Arr` Int) Empty)
t12 = (V (Proxy :: Proxy "a") `Arr` V (Proxy :: Proxy "b")) `s` Extend (Proxy :: Proxy "b") Int (Extend (Proxy :: Proxy "a") (Int `Arr` Int) Empty)

-- ### The PLAN ###
--
-- o reimplement the functionality from CircularFinal.hs
--   in terms of strongly typed islands.
-- o `unify` will get this signature: Term (is :: [k]) -> Term (is' :: [k]) -> Term (is \/ is')
-- o context lookup will be: Identifier is -> Ctx continents -> Obligations (os :: [(is, conts_n)]
-- o Can we have Contexts as type classes and terms as type aliases with "value in a context"?
