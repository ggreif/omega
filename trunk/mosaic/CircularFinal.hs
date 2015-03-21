{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts
           , ViewPatterns, TypeOperators #-}
import Prelude hiding (max, null, lookup, map)
import qualified Prelude as Prelude (max)
import Data.Map
import qualified Data.List as L
--import Data.Set hiding (singleton)
import qualified Data.Set as S
import Data.Monoid
import Data.Function

-- see: Axelsson, Klaessen: Using Circular Programs for Higher-Order Syntax
-- ICFP 2013

class LC p where
  app :: p -> p -> p
  lam :: (p -> p) -> p


-- first order interpretation

data Lam name = Var name
              | App (Lam name) (Lam name)
              | Lam name (Lam name)
              | Lam name `Cho` Lam name
  deriving Show

-- join monoid

class Join t where
  bot :: t
  prime :: t -> t
  (|-|) :: t -> t -> t

class Max lc t where
  max :: lc t -> t

instance Join name => LC (Lam name) where
  app = App
  lam f = Lam name body
    where body = f (Var name)
          name = prime (max body)

-- operator for indeterministic choice

class LC p => Indet p where
  (~~) :: p -> p -> p


instance Join Int where
  bot = 0
  prime = (+1)
  (|-|) = Prelude.max

instance Join name => Max Lam name where
  max (Var _) = bot
  max (f `App` a) = max f |-| max a
  max (a `Cho` b) = max a |-| max b
  max (Lam name _) = name


t1' :: LC p => p
t1' = lam (\a -> a `app` a)

t1 :: Lam Int
t1 = t1'

t2' :: LC p => p
t2' = lam (\a -> lam (\b -> a `app` b))

t2 :: Lam Int
t2 = t2'

t3' :: Indet p => p
t3' = lam (\a -> lam (\b -> a ~~ b))

--t3 :: Lam (Int, Int)
t3 :: (Lam Int, Lam Int)
t3 = t3'

t3'' :: (Ty Int, Ty Int, [Ty Int])
t3'' = t3'

t3''' :: Ty Int
t3''' = t3'


t0' :: Indet p => p
t0' = lam (\a -> a ~~ a)

t0 :: (Lam Int, Ty Int)
t0 = t0'

t5' :: Indet p => p
t5' = lam (\a -> lam (\b -> b ~~ b) `app` a)

t5 :: (Lam Int, Ty Int)
t5 = t5'

t6' :: LC p => p
t6' = lam (\a -> a)

t6 :: (Ty Int, Ty Int, [Ty Int])
t6 = t6'


-- ########### a very simple initial type universe ###########

data Type = Va (S.Set String) | Type `Ar` Type | Int | Cannot Type Type
  deriving (Eq, Show)

va = Va . S.singleton

can :: Type -> Bool
can Cannot{} = False
can (a `Ar` b) = can a && can b
can Int = True
can Va{} = True

infix 1 `unify`
unify :: Type -> Type -> (Type, Aliases `Map` Type)
Va a `unify` Va b | A a == A b = (a `vas` b, empty)
a `unify` b | a == b = (a, empty)
Va a `unify` Va b = (Va (a `S.union` b), empty)
Va a `unify` b = (b, a `pointsTo` b)
a `unify` Va b = (a, b `pointsTo` a)
Ar a c `unify` Ar b d = if can f && can s
     then (f `Ar` s, f' `unifion` s')
     else (Ar a c `Cannot` Ar b d, empty)
  where (f, f') = a `unify` b
        (s, s') = c `unify` d
        l `unifion` r | int <- l `intersection` r
          = case int of
            (null -> True) -> l `union` r
            overlap -> error $ "overlapping keys: " ++ show (keysSet overlap)
a `unify` b = (a `Cannot` b, empty)

pointsTo :: S.Set String -> Type -> Aliases `Map` Type
s `pointsTo` t = singleton (A s) t -- OCCURS CHECK missing, any mentions of `s` in `t`?

-- TODO: Eliminate overlaps by unification
-- TODO: utilize type system to avoid Va as values in Map
-- CHECK: add assertion that pointsTo dies not cause continent growth


-- Aliases: non-empty sets of names that are known to unify
newtype Aliases = A (S.Set String) deriving Show

instance Eq Aliases where
  A l == A r = not . S.null $ l `S.intersection` r
-- Note: this is not a transitive thing:
--       a == b /\ b == c /=> a == c, as there may not be an overlap
--       a = {1,2}, b = {2,3}, c = {3,4}

instance Monoid Aliases where
  mempty = A S.empty
  A l `mappend` A r = A $ l `S.union` r

instance Ord Aliases where
  A l `compare` A r | A l == A r = EQ
  A l `compare` A r = leader l `compare` leader r
-- Note: this is not a transitive thing, so do not expect
--       the normal indexing into a map to work
--       we have kind of a partial order, as equality messes up things
--            a < b /\ b < c => a < c only when a /= c


leader = S.elemAt 0 -- widest in scope: best
followers = tail . S.toList -- inferiors

-- assumes that the alias continents are maximal
subst :: Type -> (Aliases -> Type) -> Type
Va l `subst` f = f (A l)
Int `subst` _ = Int
Ar a b `subst` f = subst a f `Ar` subst b f
c@Cannot{} `subst` _ = c

-- assumes that the alias continents are maximal
substMap :: Type -> Aliases `Map` Type -> Type
ty `substMap` m = ty `subst` \as@(A ns) -> case as `lookup` m of Just ty -> ty; _ -> Va ns

simplify :: (Type, Aliases `Map` Type) -> Type
simplify = uncurry substMap

aliasSets :: Type -> S.Set Aliases -> S.Set Aliases
Va names `aliasSets` set = unB $ (B . S.singleton . A) names `mappend` B set
(a `Ar` b) `aliasSets` set = a `aliasSets` (b `aliasSets` set)
(a `Cannot` b) `aliasSets` set = a `aliasSets` (b `aliasSets` set)
Int `aliasSets` set = set

b = B . S.singleton . A

-- repMin-like circularity
als :: Type -> AliasSet -> (Type, AliasSet)
Va names `als` B s = (Va full, b names)
  where Just (A full) = A names `S.lookupLE` s
(a `Ar` b) `als` s = (a' `Ar` b', as `mappend` bs)
  where (a', as) = a `als` s
        (b', bs) = b `als` s
Int `als` s = (Int, B S.empty)

alsM :: Aliases `Map` Type -> AliasSet -> (Aliases `Map` Type, AliasSet)
alsM m a@(B s) = (map (fst . flip als a) (mapKeys go m), B (keysSet m))
  where go k | Just full <- k `S.lookupLE` s = full

als2 :: (Type, Aliases `Map` Type) -> AliasSet -> ((Type, Aliases `Map` Type), AliasSet)
als2 (t, m) s = ((t', m'), ts `mappend` ms)
  where (t', ts) = t `als` s
        (m', ms) = m `alsM` s

trace f t = out
   where (out, feedback) = f t feedback

wumm = trace als
mumm = trace alsM
bumm = trace als2

-- Research Q: do alias sets form sheaves/toposes?

-- AliasSet: alias-disjoint name sets
-- CAVEAT: all keys must be mutually disjoint!
--
newtype AliasSet = B (S.Set Aliases) deriving Show
unB (B b) = b

instance Monoid AliasSet where
  mempty = B mempty
  (S.toList . unB -> ls) `mappend` (B rs) = B $ ls `go` rs
     where [] `go` rs = rs
           (ls:rest) `go` rs | (sames, diffs) <- (== ls) `S.partition` rs = rest `go` S.union (smash ls sames) diffs
           smash a = S.singleton . A . S.unions . L.map (\(A s) -> s) . (a:) . S.toList

l `vas` r = Va $ l `S.union` r

v0 = va "a" `Ar` Int `unify` va "b" `Ar` va "b"
v1 = va "a" `Ar` (Int `Ar` va "a") `unify` (Int `Ar` va "b") `Ar` va "d"
v2 = va "a" `Ar` va "a" `unify` Int `Ar` Int
v3 = va "a" `Ar` (Int `Ar` va "b") `unify` va "a1" `Ar` (Int `Ar` va "b1")

aliases = (`aliasSets` S.empty)
av0 = fst v0 `aliasSets` S.empty
av1 = aliases $ fst v1
av3 = fst v3 `aliasSets` S.empty
av4 = aliases $ Va (S.fromList $ L.map return "abc") `Ar` Va (S.fromList $ L.map return "bcd")
                 `Ar` Va (S.fromList $ L.map return "ef")
av5 = aliases $ (Va (S.fromList $ L.map return "abc") `Ar` Va (S.fromList $ L.map return "def"))
                 `Ar` Va (S.fromList $ L.map return "be")
av5' = aliases $ Va (S.fromList $ L.map return "be")
                 `Ar`  (Va (S.fromList $ L.map return "abc") `Ar` Va (S.fromList $ L.map return "def"))
av51 = aliases $ Va (S.fromList $ L.map return "abc")
av52 = aliases $ Va (S.fromList $ L.map return "def")

-- ########### the pairing trick ###########

instance (LC r, LC r') => LC (r, r') where
  (f, f') `app` (a, a') = (f `app` a, f' `app` a')
  lam f = (lam f1, lam f2)
      where f1 a = fst $ f (a, undefined) -- provide a bottom
            f2 a' = snd $ f (undefined, a') -- provide a bottom

instance (Indet p, Indet p') => Indet (p, p') where
  (l, l') ~~ (r, r') = (l ~~ r, l' ~~ r')

-- ########### can we use a similar trick for type inference? ###########

instance Join name => Indet (Lam name) where
  (~~) = Cho

{-
instance Join name => Join (name, Int) where
  bot = (bot, 42)
  prime (p, x) = (prime p, x)
  (a, x) |-| (b, y) = (a |-| b, x)
-}

-- develop a vocabulary for inference
--class LC (Lam name) => Inf p name where
--  ofvar :: name -> p -- type of variable named
class LC p => Inf p where
  ofvar :: p -> p -- type of variable (must be variable!)
  equate :: p -> p -> p
  arr :: p -> p -> p

newtype Up a = Up a -- e.g. a LC one level up (vals -> tys)

instance LC p => LC (Up p) where
  Up f `app` Up a = Up $ undefined -- plan: intro an abstraction arrow and apply it on type of arg to obtain type of result


data Ty name = Univ name | Ty name `Equate` Ty name | Ty name `Arr` Ty name | Ty name `TApp` Ty name | Fresh
  deriving Show

instance Join name => Max Ty name where
  max Fresh = bot
  max (Univ _) = bot
  max (f `TApp` a) = max f |-| max a
  max (a `Equate` b) = max a |-| max b
  --max (Lam name _) = name
  max (a `Arr` b) = max a |-| max b


instance Join name => LC (Ty name) where
  f `app` a = (f `Equate` (a `Arr` Fresh)) `TApp` a
  lam f = u `Arr` body
    where u = Univ name
          body = f u
          name = prime (max body)

instance Join name => Indet (Ty name) where
  (~~) = Equate


data AllEquates = AE (Ty Int) ((Int, [Ty Int]) -> (Int, [Ty Int]))

-- ##### experiment with collecting equate constraints
instance Indet (Ty Int, Ty Int, [Ty Int]) where
  (lty, Univ l, ls) ~~ (rty, Univ r, rs) | l == r = (lty ~~ rty, Univ l, ls ++ rs)
  (lty, Univ l, ls) ~~ (rty, Univ r, rs) | l > r = (lty ~~ rty, Univ l, Univ r : ls)
  (lty, Univ l, ls) ~~ (rty, Univ r, rs) | l < r = (lty ~~ rty, Univ r, Univ l : rs)

instance LC (Ty Int, Ty Int, [Ty Int]) where
  lam f = f (arrow, u, [])
    where f1 a = fst (f (a, Univ bot, []))
          fst (a, b, c) = a
          arrow@(u@Univ{} `Arr` _) = lam f1


-- ##### have a type-level fixpoint, eliminating equated universals.
