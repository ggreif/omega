{-# LANGUAGE DataKinds, KindSignatures, FlexibleContexts, StandaloneDeriving
           , UndecidableInstances, FlexibleInstances, OverloadedStrings
           , GADTs, PatternSynonyms, TypeFamilies, RankNTypes, ViewPatterns
           , InstanceSigs, ConstraintKinds, DeriveFunctor, TypeOperators
           , PolyKinds, ImpredicativeTypes #-}

import Data.String
import Data.Function
import Unsafe.Coerce
import Prelude hiding (succ, pi)
import GHC.Exts hiding (augment)
import Debug.Trace
import Data.Type.Equality

data Nat = Z | S Nat deriving Show

class KnownNat (n :: Nat) where
  it :: Nat' n

instance KnownNat Z where
  it = Z'
instance KnownNat n => KnownNat (S n) where
  it = S' it



data Ev :: * where
  Ev :: KnownNat n => Nat' n -> Ev

natMin :: Nat' l -> Nat' r -> Nat' (l `NatMin` r)
natMin Z' r = Z'
natMin l Z' = Z'
natMin (S' l) (S' r) = S' (natMin l r)


natEq :: Nat' l -> Nat' r -> Maybe (l :~: r)
natEq Z' Z' = Just Refl
natEq (S' l) (S' r) = do Refl <- natEq l r; return Refl
natEq _ _ = Nothing

ev :: KnownNat result => Nat' l -> Nat' r -> Nat' result -> Maybe (result :~: NatMin l r)
ev l r res = case (natMin l r, Ev res) of
                  (lr, Ev res') -> do Refl <- lr `natEq` res; Refl <- res `natEq` res'; return Refl


-- Alternative: Use Maybe Nat for the storeys
type family Climb (n :: Maybe Nat) :: Maybe Nat where
  Climb Nothing = Nothing
  Climb (Just (S n)) = Just n

type family Succ (n :: Maybe Nat) :: Maybe Nat where
  Succ Nothing = Nothing
  Succ (Just n) = Just (S n)

type family Min (l :: Maybe Nat) (r :: Maybe Nat) :: Maybe Nat where
  Min Nothing r = r
  Min l Nothing = l
  Min (Just Z) r = Just Z
  Min l (Just Z) = Just Z
  Min (Just (S l)) (Just (S r)) = Just (S (NatMin l r))

type family NatMin (l :: Nat) (r :: Nat) :: Nat where
  NatMin Z r = Z
  NatMin l Z = Z
  NatMin (S l) (S r) = S (NatMin l r)

type family Plus (l :: Nat) (r :: Nat) :: Nat where
  Plus Z r = r
  Plus (S l) r = S (Plus l r)

type UZ = Just Z

class Card (rep :: Maybe Nat -> *) where
  infty :: rep Nothing
  zero :: rep UZ
  succ :: rep p -> rep (Succ p)

newtype UNatStr (sem :: Maybe Nat) = UNatStr String deriving Show
instance Card UNatStr where
  infty = UNatStr "oo"
  zero = UNatStr "0"
  succ (UNatStr p) = UNatStr $ 'S' : p

data UNat (sem :: Maybe Nat) where
  Ze :: UNat (Just Z)
  Su :: UNat (Just n) -> UNat (Just (S n))
  Inf :: UNat Nothing

instance Card UNat where
  infty = Inf
  zero = Ze
  succ Ze = Su Ze
  succ (Su a) = Su (Su a)
  succ Inf = Inf

deriving instance Show (UNat sem)

data Tw (from :: Nat) (to :: Maybe Nat) = Tw (Nat' from) (UNat to) deriving Show

up :: Tw from to -> Tw (S from) (Climb to)
up (Tw n m) = Tw (S' n) (pred m)
  where pred :: UNat m -> UNat (Climb m)
        pred Inf = Inf
        pred (Su p) = p

data Nat' :: Nat -> * where
  Z' :: Nat' Z
  S' :: Nat' n -> Nat' (S n)

deriving instance Show (Nat' n)

nat2int :: Nat' n -> Int
nat2int Z' = 0
nat2int (S' n) = 1 + nat2int n

-- --------------+ at  -+ room
--               v      v
class LC (rep :: Nat -> Maybe Nat -> *) where
  var :: rep n m
  lam' :: Nat' d -> rep n m -> rep n m
  app :: rep n m -> rep n m' -> rep n (Min m m')

-- helpers
lam :: LC rep => rep Z Nothing -> rep Z Nothing
lam = lam' (S' Z')

lAM :: LC rep => rep (S Z) Nothing -> rep (S Z) Nothing
lAM = lam' $ S' (S' Z')

class TypedLC (rep :: Nat -> Maybe Nat -> *) where
  annot :: rep n m -> rep (S n) m -> rep n m
  typeof :: rep n m -> rep (S n) (Climb m)

class BuiltinLC (rep :: Nat -> Maybe Nat -> *) where
  star :: rep (S (S n)) Nothing
  int :: rep (S n) Nothing
  io :: rep (S Z) UZ
  cnst :: Int -> rep Z Nothing

-- ##############
--     Pairing
-- ##############

data P (rep :: Nat -> Maybe Nat -> *) (rep' :: Nat -> Maybe Nat -> *) at room = P !(rep at room) !(rep' at room)

instance (LC rep, LC rep') => LC (P rep rep') where
  var = P var var
  lam' d (P body body') = P (lam' d body) (lam' d body')
  app (P f f') (P a a') = P (f `app` a) (f' `app` a')

-- ##############
--     TypeOf
-- ##############

newtype TypeOf (rep :: Nat -> Maybe Nat -> *) (n :: Nat) (m :: Maybe Nat) = T (rep (S n) Nothing) -- So far all type-y result things are unbounded

unT (T t) = t

deriving instance Show (rep (S n) Nothing) => Show (TypeOf rep n m)

instance (LC rep, TypedLC rep, BuiltinLC rep) => LC (TypeOf rep) where
  var = T int
  lam' Z' body = body -- factually a Pi
  lam' (S' n) (T body) = T $ lam' n body
  app (T f) _ = T f -- FIXME: dependent types? -- substitute argument into f's body

instance BuiltinLC rep => TypedLC (TypeOf rep) where
  --annot etc. --> TODO

instance (LC rep, BuiltinLC rep) => BuiltinLC (TypeOf rep) where
  star = T star
  int = T star
  cnst _ = T int
  io = T $ lam' Z' star


-- ## TESTS ##

t1, t2 :: LC rep => rep Z Nothing
t1 = lam var
t2 = t1 `app` t1

t3 :: (LC rep, BuiltinLC rep) => rep Z Nothing
t3 = t1 `app` cnst 42

t4 :: (LC rep, BuiltinLC rep) => rep (S Z) UZ
t4 = io `app` int

newtype Levelled a (n :: Nat) (m :: Maybe Nat) = L { unL :: a } --deriving Show

type LString = Levelled String
deriving instance Show (LString n m)

raise f = unL . f . L

instance IsString (LString n m) where
  fromString = L

instance {-HasLevel (LString n) => -}LC LString where
  var = {-addLevel $-} "?"
  lam' Z' body = L $ "(|| " ++ unL body ++ ")"
  lam' (S' Z') body = L $ "(\\ " ++ unL body ++ ")"
  lam' (nat2int -> n) body = L $ "(" ++ show n ++ "\\ " ++ unL body ++ ")"
  app e1 e2 = L $ "(" ++ unL e1 ++ " " ++ unL e2 ++ ")"

{-
class HasLevel p where
  addLevel :: p -> p
  level :: p -> Int

instance HasLevel (LString Z) where
  addLevel p = unL p ++ "@" ++ (show . level) p
  level _ = 0

instance HasLevel (LString n) => HasLevel (LString (S n)) where
  addLevel p = unL p ++ "@" ++ (show . level) p
  level _ = 1
-}

instance BuiltinLC LString where
  cnst i = L $ show i
  star = "*"
  int = "Int"
  io = "IO"

instance TypedLC LString where
  --TODO


instance LC Tw where
  var = Tw undefined undefined -- Inf


-- ############
--     Eval
-- ############

-- context can hold one binding at most :-)
--
--                                 context ~~~~~vvvvvvv    v~~~~~ result
newtype Eval a (n :: Nat) (m :: Maybe Nat) = E (Maybe a -> a)

instance Show a => Show (Eval a n m) where
  show (E f) = show $ f Nothing

instance LC (Eval a) where
  var = E $ \(Just a) -> a
  lam' (S' Z') body = body
  app (E f) (E a) = let a' = a Nothing in E $ \Nothing -> f $ Just a'

instance BuiltinLC (Eval Int) where
  cnst i = E $ const i

-- a small test: (\x->x) 42
--
e1, e2 :: Eval Int Z Nothing
e1 = lam var `app` cnst 42
e2 = lam (cnst 25) `app` cnst 42


-- ## Constructors ##

-- we want to write to write:

data Nut :: * where {Y::Nut; R::Nut->Nut}

class Data (rep :: Nat -> Maybe Nat -> *) where
  dat :: rep (S (S l)) Nothing -> String -> rep (S l) Nothing -> ep l Nothing

--d1 :: rep (S Z) Nothing

-- in Initial representation we would have

type Sig = String -- for now
data Defn (bod :: Bool) (dat :: Bool)  (con :: Bool) (lev :: Nat) where
  Postulate :: Defn True False False lev
  Data :: String -> Sig -> Defn False dat con lev -> Defn False True False (S lev)
  Constr :: String -> Sig -> Defn False False True lev
  Func :: String -> Sig -> Defn True False False lev -> Defn False False False lev


y = Data "Nut" "*" (Constr "Y" "Nut")
r = Data "Nut" "*" (Constr "R" "Nut->Nut")
forw = Func "timestwo" "Nat->Nat" Postulate
mutual = Data "Mut" "*" (Func "foo" "Mut->Mut" Postulate) -- Agda style?
nested = Data "Nest" "*" (Data "N1" "Nest" (Data "N2" "N1" (Constr "C3" "N2")))


---- Some PHOAS ideas (playing around)

-- represent binders with some lambda where the domain is sufficiently parametric
-- i.e. "\a->2*x" --> \(bound :: p) -> 2 * bound

class PLC (rep :: Nat -> Maybe Nat -> *) where
  type Inspectable (rep :: Nat -> Maybe Nat -> *) (i :: Nat -> Maybe Nat -> *) :: Constraint
  type Inspectable rep a = Augment rep ~ a
  data Augment rep :: Nat -> Maybe Nat -> *
  pvar :: Inspectable rep p => p n m -> Augment rep n m
  plam :: Nat' d -> (forall p . Inspectable rep p => p n m -> Augment rep n m) -> rep n m
  ep :: (rep n m -> Augment rep n m, Augment rep n m -> rep n m) -- embedding/projection pair

-- lifting helpers
lift f = fst ep . f . snd ep
unlift f = snd ep . f . fst ep
augment f = fst ep . f
--shrink :: PLC rep => (rep n m -> Augment rep n m) -> (rep n m -> rep n m)
--shrink f = snd ep . f
testss :: Int -> a
testss = undefined

-- parametric lambda (helper)
pla :: PLC rep => (rep n m -> rep n m) -> rep n m
pla f = plam (S' Z') (lift f . pvar)


pl0,pl1,pl2,pl2a,pl3,pl4,pl5,pl5a,pl6a,pl10 :: (LC rep, BuiltinLC rep, PLC rep) => rep Z Nothing
pl0 = pla $ \x -> x
pl1 = pla (\x -> x `app` x)
pl1' :: LString Z Nothing
pl1' = pl1

pl2 = pla $ \x -> pla $ \y -> y `app` x
pl2a = pla $ \x -> pla $ \y -> cnst 45
pl3 = pla $ \x -> pla $ \y -> pla $ \z -> y `app` x
pl10 = pl3 `app` pl0 `app` pl0 `app` pl0


pl4 = pl0 `app` cnst 4
pl5 = pl2 `app` cnst 4 `app` pl0
pl5a = pl2a `app` cnst 4 `app` cnst 3
pl6a = pla (\x->pl2a) `app` cnst 4 `app` cnst 3 `app` cnst 1

instance PLC LString where
  pvar = id
  plam (S' Z') f = L ("\\a." ++ (raise (unlift f) "a"))


type NameSupply = Levelled ([String] -> String)

instance LC NameSupply where
  L f `app` L a = L (\ns -> "(" ++ f ns ++ " " ++ a ns ++ ")")

instance TypedLC NameSupply where

instance BuiltinLC NameSupply where
  star = L . const $ "*"
  int = L . const $ "Int"
  cnst i = L . const . show $ i

instance PLC NameSupply where
  pvar = id
  plam :: Nat' d -> (forall p . Inspectable NameSupply p => p n m -> Augment NameSupply n m) -> NameSupply n m
  plam Z' f = L $ \(n:ns) -> "||" ++ n ++ "." ++ unL (unlift f . L . const $ n) ns
  plam (S' Z') f = L $ \(n:ns) -> "\\" ++ n ++ "." ++ unL (unlift f . L . const $ n) ns
  newtype Augment NameSupply n m = A { unA :: NameSupply n m }
  ep = (A, unA)

instance Show (NameSupply n m) where
  show (L f) = f $ map (('v':) . show) [0..]

-- List-Env evaluation
--
data Evaler a n = forall m . Evaler (EvalL a n m -> EvalL a n m)
--newtype EvalL a n m = Env { unEnv :: Levelled ([Either (EvalL a n m -> EvalL a n m) a] -> Either (EvalL a n m -> EvalL a n m) a) n m }
newtype EvalL a n m = Env { unEnv :: Levelled ([Either (Evaler a n) a] -> Either (Evaler a n) a) n m }
instance Show a => Show (Evaler a n) where
  show = const "CLOSURE"
instance Show a => Show (EvalL a n m) where
  show (Env (L f)) = show $ f $ []

instance PLC (EvalL a) where
  pvar = id
  plam :: Nat' d -> (forall p . Inspectable (EvalL a) p => p n m -> Augment (EvalL a) n m) -> (EvalL a) n m
  plam (S' Z') f = Env . L $ feed
    where feed (v:vs) = (unL . unEnv) (unlift f . Env . L . const $ v) vs
          feed [] = Left $ Evaler (unlift f)
  newtype Augment (EvalL a) n m = Deeper { unDeeper :: EvalL a n m }
  ep = (Deeper, unDeeper)

instance LC (EvalL a) where
  Env (L f) `app` Env (L a) = Env . L $ \vs -> let av = a vs in f $ av:vs

instance BuiltinLC (EvalL Int) where
  cnst i = Env . L . const . Right $ i


instance PLC (Eval a) where
  pvar = id
  plam :: Nat' d -> (forall p . Inspectable (Eval a) p => p n m -> Augment (Eval a) n m) -> Eval a n m
  plam (S' Z') f = E $ \(Just v) -> unE (unlift f . E . const $ v) Nothing

unE (E l) = l

pe1, pe2 :: Eval Int Z Nothing
pe1 = pla id `app` cnst 42
pe2 = pla (\_ -> cnst 25) `app` cnst 42

-- TypeOf for PHOAS
instance (BuiltinLC rep, PLC rep) => PLC (TypeOf rep) where
  pvar = id
  plam Z' f = unlift f . T $ int -- factually a Pi
  plam (S' n) f = T $ plam n $ augment $ \x -> unT . unlift f . T $ int
  newtype Augment (TypeOf rep) n m = InnerTypeOf { unInnerTypeOf :: TypeOf rep n m }
  ep = (InnerTypeOf, unInnerTypeOf)

-- TODOs:
--  o Num instances
--  o TyEnv :: [*] -> *, simply typed LC (we need a non-trivial Augment for this)
--  o Type inference
--  o Emax-style unityped->typed compiler (Emil Axelsson)
--  o Shape :: LambdaTree(Graph) -> *, shapely LC
--  o PHOAS <--> DeBruijn conversions

-- Anonymous datatypes
-----------------------

{-
Here is the story:

Model data types as (type)functions

ty :: Nat -> [*] -> *
ty 0 [_] = Nat' Z
ty 1 [Nat n] = (Nat' n -> Nat' (S n))

-}

type family Na (alt :: Nat) (env :: [*]) where
  Na Z ignore = Nat' Z -- Z' :: Nat' Z
  Na (S Z) '[Nat' n] = (Nat' n -> Nat' (S n)) -- S :: ...
  --Na (S Z) '[] = (Nat' n -> Nat' (S n)) -- S :: ...

type family Tup arr where
  Tup (a -> b -> c) = (a, b)
  Tup (a -> b) = a
  Tup a = ()

data Fin :: Nat -> Nat -> * where
  FZ :: Fin (S m) Z
  FS :: Fin m n -> Fin (S m) (S n)


data Anon :: Nat -> [*] -> (Nat -> [*] -> *) -> * where
  Constru :: Fin max con -> Tup (t con prms) -> Anon max prms t

type Nuzz n = Anon (S (S Z)) '[Nat' n] Na

z'' :: Nuzz n
z'' = Constru FZ ()
s'' = Constru (FS FZ) () -- FIXME