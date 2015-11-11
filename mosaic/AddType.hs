{-# LANGUAGE ViewPatterns, KindSignatures, GADTs, PolyKinds, StandaloneDeriving, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, TypeFamilies, PatternSynonyms, FunctionalDependencies, RankNTypes, UndecidableInstances #-}
{-# LANGUAGE DataKinds, TypeOperators #-} -- 7.10??
{-# LANGUAGE InstanceSigs #-}

module AddType where

import Data.Functor.Identity
--import Control.Category(Category)
--import qualified Control.Category as Cat (Category(id, (.)))
import Control.Applicative (liftA2)
import Unsafe.Coerce(unsafeCoerce)
import Data.Proxy
import Data.Coerce
import Data.Type.Equality

data Nat = Z | S Nat deriving Show

plus :: Nat -> Nat -> Nat
plus Z = id
plus (S (plus -> f)) = f . S

type Constr0 = Constr' Z Nat
pattern ConstrZ :: Constr0 Z
pattern ConstrZ = Constr'

deriving instance Show (Constr0 Z)

type Constr1 = Constr' (S Z) (Nat->Nat)
pattern ConstrS :: Constr1 S
pattern ConstrS = Constr'

data Constr' (tag :: Nat) (typ :: *) (coarg :: k) where
  Constr' :: Tor ca tag typ => Constr' tag typ ca

deriving instance Show (Constr1 S)

data Plus (arg :: Nat) (coarg :: Nat -> Nat) where
  PlusZ :: Plus Z f
  PlusS :: {-(Plus n `Compose` Constr1) f ->-} Plus (S n) f

-- Idea: it should be a purely mechanical process to follow the types and create corresponding values,
--       so when the algorithm is encoded in the type, then classes should build inhabitants.
--

class {-Category sig =>-} Machine (sig :: * -> *) where
  -- have composition, un/tagging, calling (application)
  app :: sig (a -> b) -> sig a -> sig b
  entag :: Constr' tag typ ca -> sig typ
  detag :: Tor ca tag typ => expr ca f -> sig typ
  --detag :: Tor Z tag typ => Plus Z f -> sig typ
  --detag1 :: Tor S tag typ => Plus (S a) f -> sig typ -- typ ^ -1 ???
  ---detag1 :: Tor ca tag typ => expr (ca a) f -> sig typ -- typ ^ -1 ???
  detagWith :: Constr' tag (a->b) (ca :: c -> c) -> sig b -> sig a
  ident :: sig (a -> a)
  comp :: sig (b -> c) -> sig (a -> b) -> sig (a -> c)
  pure' :: a -> sig a
  grab :: (sig a -> sig b) -> sig (a -> b)


data Code (tres :: *)
instance Machine (Code)

class Tor (ca :: k) (tag :: Nat) typ | ca -> tag typ, tag typ -> ca where
  cfun :: Constr' tag typ ca -> typ

instance Tor Z Z Nat where
  cfun Constr' = Z

instance Tor S (S Z) (Nat -> Nat) where
  cfun Constr' = S


instance Machine Identity where
  Identity f `app` Identity a = pure $ f a
  entag c@Constr' = pure (cfun c)
  ident = pure id
  comp = liftA2 (.)
  pure' = pure
  grab = coerce

class Smurf (f :: k -> *) (papa :: *) | f -> papa where
  smurf :: Machine m => f r -> m papa

instance Smurf (Constr' tag typ) typ where
  smurf c@Constr' = entag c

instance Smurf (Plus Z) (Nat -> Nat) where
  smurf PlusZ = ident


-- ####### frobbed from Data.Reflection #########
class Given typ (a :: k -> *) | a -> typ where
  -- | Recover the value of a given type previously encoded with 'give'.
  given :: Jokey typ a coarg

newtype Jokey (typ :: *) (a :: k -> *) coarg = Jokey (forall m . m typ)

newtype Gift m typ a = Gift (Given typ a => m typ)


give :: forall a m sig . Proxy a -> m sig -> (Given sig a => m sig) -> m sig
give _ a k = unsafeCoerce (Gift k :: Gift m sig a) a
-- ################

instance Smurf (Jokey typ bla) typ where
  smurf (Jokey present) = present

deriving instance Show (Plus a c)

data Compose (a1 :: (b -> c) -> *) (a0 :: (a -> b) -> *) (coarg :: a -> c) where
  Compose :: (Show (f a), Show (g b)) => g b -> f a -> Compose g f c

deriving instance Show (Compose g f c)

data Match2 (c0 :: k -> *) (c1 :: k -> *) (out :: k) where
  Match2 :: (Show (x ca a), Show (c1 a), Tor ca tag typ) => x ca a -> c1 a -> Match2 (x ca) c1 a

deriving instance Show (Match2 g f c)

instance (Smurf c0 papa, Smurf c1 papa) => Smurf (c0 `Match2` c1) papa where
  --smurf = error "implement in terms of detag"
  smurf (c0 `Match2` c1) = smurf c0

-- can we now define Plus completely?

--data Def (d :: Nat -> (Nat -> Nat) -> *) (f :: Nat -> Nat -> Nat)
data Def (d :: k -> l -> *) (f :: k -> l)

instance Smurf (Def Plus) (Nat -> Nat -> Nat) where
  -- smurf _ = grab (const $ smurf (PlusZ `Match2` PlusZ)) -- machine needs to give support: grab first arg and pass it to Match2?

-- Match2 lifts
  --      two    Plus :: Nat -> (Nat -> Nat) -> *
  --      to be  (Match2 (Plus Z)) :: ((Nat -> Nat) -> *) -> (Nat -> Nat) -> *
  --      to be  (Match2 (Plus Z) (Plus (S Z))) :: (Nat -> Nat) -> *

-- Suppose we have a (Plus n) assuming n = S m, we want to bind that m *on the type level*
--  Bind (forall m . (S m ~ n) => something with m)
-- type-level HOAS?

--foo :: P n -> (forall m . P m

--lam :: forall a . (a -> a) -> a

-- Consider
--     Plus Z `Match2` Plus (S m)

-- match figures out n == S m, if so calls the lambda.
-- Clearly no lambdas, so it needs to call a partially-applied type

--     Plus Z `Match2` (Lam (\m -> Plus (S m))

-- the Lam should give us the smurfed thing (value/type) instead of the (type/kind)

--type XXX = Plus Z `Match2` (forall m . Plus (S m))

{-
How about Match2 expressing a fixpoint smurf-wise?

Write type function:

baz (Constr Z 0 Nat) (Plus Z) -> (Nat->Nat)
baz (Constr S 1 (Nat->Nat)) (Plus (S m)) -> (Nat*->Nat->Nat)

where Nat* is the extra argument being equal to (Plus m)
-}

{-
type family Baz con expr where
  --Baz (Constr' tag typ ca) (hd ca) = typ  -- hd :: typ -> Papa (hd ca)
  Baz (Constr' tag typ ca) (hd ca) = Papa (hd ca)
  --Baz (Constr' tag (fro->to) ca) (hd (ca junk)) = fro->to -- hd : to -> Papa (hd (ca junk))

  Baz (Constr' tag (fro->to) ca) (hd (ca arg)) = fro -> Papa (hd (ca arg))
-}

--data SamePapa hd a b where
--  Same :: (Papa (hd a) ~ Papa (hd b)) => Proxy a -> Proxy b -> SamePapa hd a b

{-

data Alt (hd :: k -> (k -> l) -> *) (coarg :: k -> k -> l) where
  (:=>) :: Constr' tag typ ca -> hd ca f -> Alt hd f'
  (:==>) :: Constr' tag typ ca -> hd (ca a) f -> Alt hd f'
  --Tri :: (Papa (hd (ca a)) ~ bla) => Constr' tag typ ca -> hd (ca a) f -> (forall m . (Machine m, Given bla (hd a)) => hd (ca a) f -> m bla) -> Alt f
  --Tri :: Constr' tag typ ca -> (forall a . Proxy (hd a)) -> (forall a . hd (ca a) (f a)) -> (forall a . SamePapa hd (ca a) a) -> (forall a m . (Machine m, Papa (hd (ca a)) ~ Papa (hd a), Given (Papa (hd (ca a))) (hd a)) => hd (ca a) (f a) -> m (Papa (hd (ca a)))) -> Alt hd f
  Tri :: Constr' tag typ ca -> (forall a . Proxy (hd a)) -> (forall a . hd (ca a) (f a)) -> (forall a m . (Machine m, Papa (hd (ca a)) ~ Papa (hd a), Given (Papa (hd (ca a))) (hd a)) => hd (ca a) (f a) -> m (Papa (hd (ca a)))) -> Alt hd f


a0 = ConstrZ :=> PlusZ
a1 = ConstrS :==> PlusS
--a1' = Tri ConstrS Proxy PlusS (unsafeCoerce (Same (Proxy Proxy)) smurf
a1' = Tri ConstrS Proxy PlusS smurf

-}

instance Smurf (Def hd) (arg->res) => Smurf (Alt arg res hd) (arg->res) where
  smurf (Tri con@Constr' (prox :: Proxy (hd a)) (fun :: hd (ca a) (f a)) sm)
       = grab (\arg -> give prox (smurf (undefined :: Def hd f) `app` (detagWith con arg)) (sm fun))


instance Given (Nat->Nat) (Plus n) => Smurf (Plus (S n)) (Nat->Nat) where
  smurf (PlusS :: Plus (S n) f) = plusN `comp` entag ConstrS
    where plusN = smurf (given :: Jokey (Nat->Nat) (Plus n) f)


data Alt (arg :: *) (res :: *) (hd :: k -> (k -> l) -> *) (coarg :: k -> k -> l) where
  Tri :: Smurf (Def hd) (arg->res) => Constr' tag (arg->arg) ca -> (forall a . Proxy (hd a)) -> (forall a . hd (ca a) (f a)) -> (forall a m . (Machine m, Given res (hd a)) => hd (ca a) (f a) -> m res) -> Alt arg res hd f

a1 = Tri ConstrS Proxy PlusS smurf
