{-# LANGUAGE ViewPatterns, KindSignatures, GADTs, PolyKinds, StandaloneDeriving, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, TypeFamilies, PatternSynonyms, FunctionalDependencies #-}
{-# LANGUAGE DataKinds, TypeOperators #-} -- 7.10??

module AddType where

import Data.Functor.Identity
--import Control.Category(Category)
--import qualified Control.Category as Cat (Category(id, (.)))
import Control.Applicative (liftA2)

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

data Free (var :: k) (coarg :: k)

class IdLike (transform :: k -> k -> *)

data Plus (arg :: Nat) (coarg :: Nat -> Nat) where
  PlusZ :: Id (f Z) (f Z) -> Plus Z f
  --PlusS :: Smurf (Free n) => (Plus n `Compose` Constr1) f -> Plus (S n) f -- FIXME
  --PlusS :: Smurf (Plus n) => (Plus n `Compose` Constr1) f -> Plus (S n) f -- FIXME
  ---PlusS :: (IdLike eeek, Smurf (eeek n)) => (Plus n `Compose` Constr1) f -> Plus (S n) f -- FIXME
  PlusS :: (eeek ~ Free, Smurf ((eeek :: Nat -> Nat -> *) n)) => (Plus n `Compose` Constr1) f -> Plus (S n) f -- FIXME
  --        ^^ should this be value inference?
  --PlusS' :: Plus n f -> Plus (S n) f
  --PlusS :: (Plus Z `Match2` Plus (S m)) f -> Plus (S n) f

-- Idea: it should be a purely mechanical process to follow the types and create corresponding values,
--       so when the algorithm is encoded in the type, then classes should build inhabitants.
--

class {-Category sig =>-} Machine (sig :: * -> *) where
  -- have composition, un/tagging, calling (application)
  app :: sig (a -> b) -> sig a -> sig b
  entag :: Constr' tag typ ca -> sig typ
  detag :: Tor ca tag typ => expr ca f -> sig typ
  --detag :: Tor Z tag typ => Plus Z f -> sig typ
  ident :: sig (a -> a)
  comp :: sig (b -> c) -> sig (a -> b) -> sig (a -> c)


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

class Smurf (f :: k -> *) where
  type Papa f :: *
  smurf :: Machine m => f r -> m (Papa f)

instance Smurf (Constr' tag typ) where
  type Papa (Constr' tag typ) = typ
  smurf c@Constr' = entag c

instance Smurf (Plus Z) where
  type Papa (Plus Z) = Nat -> Nat
  smurf (PlusZ _) = ident

instance Smurf (Plus (S n)) where
  type Papa (Plus (S n)) = Nat -> Nat
  --smurf (PlusS _) = entag ConstrS `comp` entag ConstrS
  smurf (PlusS less) = smurf less `comp` entag ConstrS

--instance (Value (f a), Value (g b)) => Value ((g b `Compose` f a) c) where

--instance (Show (c0 a), Show (c1 a), Value (c0 a), Value (c1 a)) => Value (Match2 c0 c1 a) where
--  val = Match2 (val :: c0 a) (val :: c1 a)

deriving instance Show (Plus a c)

data Id (arg :: k) (coarg :: k) where
  Id :: Id x x

deriving instance Show (Id a c)

data Compose (a1 :: (b -> c) -> *) (a0 :: (a -> b) -> *) (coarg :: a -> c) where
  Compose :: (Show (f a), Show (g b)) => g b -> f a -> Compose g f c

deriving instance Show (Compose g f c)

data Match2 (c0 :: k -> *) (c1 :: k -> *) (out :: k) where
  Match2 :: (Show (x ca a), Show (c1 a), Tor ca tag typ) => x ca a -> c1 a -> Match2 (x ca) c1 a

deriving instance Show (Match2 g f c)

instance (Smurf c0, Smurf c1) => Smurf (c0 `Match2` c1) where
  type Papa (c0 `Match2` c1) = Papa c0
  --smurf = error "implement in terms of detag"
  smurf (c0 `Match2` c1) = smurf c0



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

type family Baz con expr where
  --Baz (Constr' tag typ ca) (hd ca) = typ  -- hd :: typ -> Papa (hd ca)
  Baz (Constr' tag typ ca) (hd ca) = Papa (hd ca)
  --Baz (Constr' tag (fro->to) ca) (hd (ca junk)) = fro->to -- hd : to -> Papa (hd (ca junk))

  Baz (Constr' tag (fro->to) ca) (hd (ca arg)) = fro -> Papa (hd (ca arg))


data Alt (coarg :: k -> l) where
  (:=>) :: Constr' tag typ ca -> hd ca f -> Alt f
  (:==>) :: Constr' tag typ ca -> hd (ca a) f -> Alt f

instance Smurf Alt where
  -- smurf (Constr' :=> )

a0 = ConstrZ :=> PlusZ Id
a1 = ConstrS :==> PlusS undefined
