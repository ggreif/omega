-- Time-stamp: <2010-05-14 11:08:06 cklin>

module Substitution where

import Data.List ((\\), union)
import qualified Data.Map as Map

import Types
import Common
import Monad

--------- General substitution utility functions

-- Construct a substitution.  This factory function checks that the
-- mapping is idempotent and reports an error otherwise.  Note that
-- compoSub (and perhaps other too) can produce identity mappings (e.g.,
-- [x/x]) in the associative list, so the algorithm must sanitize the
-- mapping (to mp0) to avoid tripping the idempotency checking.

makeSub :: [(Int, Type)] -> Subst
makeSub mp =
    let mp0 = filter (\(i, t) -> TyMeta i /= t) mp
        dom = map fst mp0
        rng = unionMap (metaType . snd) mp0
    in if overlaps dom rng
       then bug "Mapping is not idempotent"
       else toMap mp0

zeroSub :: Subst
zeroSub = Map.empty

oneSub :: Int -> Type -> Subst
oneSub = Map.singleton

nullSub :: Subst -> Bool
nullSub = Map.null

-- Compute the domain and the range of a substitution.

domSub :: Subst -> [Int]
domSub = Map.keys

rngSub :: Subst -> [Type]
rngSub = Map.elems

metaSub :: Subst -> [Int]
metaSub sub = domSub sub `union` metaTypes (rngSub sub)

-- Apply a substitution to a type.  Since substitution mappings are
-- idempotent, there is no need for iterative application.

zonk :: Subst -> Endo Type
zonk sub = replace where
    replace (TyCon tc ax) = TyCon tc (map replace ax)
    replace t@(TyMeta i) = Map.findWithDefault t i sub
    replace (TySkol i) | Map.member i sub =
        bug "Substitution on Skolem type"
    replace t = t

-- Apply a substitution directly to a meta type variable index.

zonkIndex :: Subst -> Int -> Type
zonkIndex sub i = Map.findWithDefault (TyMeta i) i sub

-- Rename meta type variables in a type.  Unlike substitutions, this
-- dedicated renaming function does not care about the orientation of
-- type variable renaming.

renameMeta :: Rename -> Endo Type
renameMeta ren = replace where
    replace (TyCon tc ax) = TyCon tc (map replace ax)
    replace (TyMeta i) = TyMeta (lookupZ i ren)
    replace t = t

-- Replace free type variables with (supposedly fresh) meta type
-- variables.  Not strictly a substitution, but ...

instType :: Map.Map Ident Int -> Endo Type
instType inst = replace where
    replace (TyCon tc ax) = TyCon tc (map replace ax)
    replace (TyVar tv) = TyMeta (lookupX tv inst)
    replace t = t

-- Compute a substitution that forces the second type (t) to have the
-- same top-level type constructor as the first type (c) .

imprintTc :: Type -> Type -> Ti Subst
imprintTc c t =
    do u <- freshenTyCon c
       unify2 u t

-- The skolemize function computes a substitution that replaces meta
-- type variables with Skolem types that have the same indices.  The
-- unskolemize function replace Skolem types to their corresponding meta
-- type variables.

skolemize :: [Int] -> Subst
skolemize = makeSub . map skol
    where skol m = (m, TySkol m)

unskolemize :: Endo Type
unskolemize = replace where
    replace (TyCon tc ax) = TyCon tc (map replace ax)
    replace (TySkol i) = TyMeta i
    replace t = t

-- Compose two substitutions.  The function uses nub1st to arbitrate
-- (favoring sub2) when the domains overlap.  Composition is not
-- commutative, and tv(rng(sub1)) must be disjoint from dom(sub2) with
-- the exception of reverse renaming (see example).
-- zonk sub1 (zonk sub2 t) == zonk (compoSub sub1 sub2) t
-- compoSub [x/y] [y/x] == [x/y]

compoSub :: Subst -> Endo Subst
compoSub sub1 sub2 = makeSub (nub1st (mp2 ++ mp1)) where
    mp1 = Map.toList sub1
    mp2 = Map.toList (Map.map (zonk sub1) sub2)

compoSubs :: [Subst] -> Subst
compoSubs = foldl compoSub zeroSub

-- Restrict the domain of a substitution.

restrictSub :: [Int] -> Endo Subst
restrictSub mx = Map.filterWithKey relevant
    where relevant i _ = i `elem` mx

-- Apply an idempotent variable renaming to a both the domain and the
-- range of a substitution.  Here is an example:
-- switchMetaSub [a/x, b/y] [T x/y] == [T a/b]

switchMetaSub :: Rename -> Endo Subst
switchMetaSub ren = makeSub . map switch . Map.toList
    where switch (i, t) = (lookupZ i ren, renameMeta ren t)

-- Restrict an idempotent substitution to the parts that have nontrivial
-- effects on the given set of type variables.  More specifically, the
-- function restricts the domain to the type variables of interest, and
-- then it eliminates trivial type variable mappings (i.e., renaming).

shaveSub :: [Int] -> Endo Subst
shaveSub mx sub = shaven where
    trimmed = restrictSub mx sub
    nontriv = multiP (rngSub trimmed)
    keep (TyMeta i) = nontriv i || elem i mx
    keep _          = True
    shaven = Map.filter keep trimmed          

-- Extend a substitution such that every meta type variable in the input
-- list dom is in the domain of the extended subsitution.

divertSub :: [Int] -> EndoTi Subst
divertSub dom sub =
    do let gap = dom \\ domSub sub
       fresh <- freshenTv gap
       let fill = makeSub (zip gap fresh)
       return (compoSub fill sub)

--------- Plain unification functions

unify :: [Type2] -> Ti Subst
unify [] = return zeroSub
unify ((t1, t2):tx) =
    do this <- unify2 t1 t2
       let norm (u1, u2) = (zonk this u1, zonk this u2)
       rest <- unify (map norm tx)
       return (compoSub rest this)

unify2 :: Type -> Type -> Ti Subst
unify2 (TyVar _) _ = bug "Bound type variable in unify2"
unify2 _ (TyVar _) = bug "Bound type variable in unify2"
unify2 (TyMeta i1) (TyMeta i2) | i1 == i2 = return zeroSub
unify2 (TyMeta i1) t2 = unifyMeta i1 t2
unify2 t1 (TyMeta i2) = unifyMeta i2 t1
unify2 (TySkol i1) (TySkol i2) | i1 == i2 = return zeroSub
unify2 (TySkol _) _ = fail "Cannot unify with a Skolem type"
unify2 _ (TySkol _) = fail "Cannot unify with a Skolem type"
unify2 (TyCon tc1 ax1) (TyCon tc2 ax2) =
    if tc1 == tc2 && length ax1 == length ax2
    then unify (magic $ zip ax1 ax2)
    else fail "Cannot unify different type constructors"

unifyMeta :: Int -> Type -> Ti Subst
unifyMeta i t =
    if elem i (metaType t)
    then fail "Unification produces an infinite type"
    else return (oneSub i t)

unifyTypes :: [Type] -> Ti Subst
unifyTypes [] = unify []
unifyTypes tx = unify (zip (tail tx) tx)

-- Unifiability testing.  If the given type equations / types are
-- satisfiable, return a most-general unifier as evidence.  The function
-- uses trapTi to present a non-monadic interface.

unifiable :: [Type2] -> Maybe Subst
unifiable = trapTi . unify

unifiableTypes :: [Type] -> Maybe Subst
unifiableTypes = trapTi . unifyTypes

--------- Substitution unification algorithm

-- Compute a most-general common instance of the input substitutions.
-- This algorithm is so much simpler than McAdam's substitution
-- unification, and it extends naturally to more than two substitutions.

combineSub :: Subst -> EndoTi Subst
combineSub sub1 sub2 = combineSubs [sub1, sub2]

combineSubs :: [Subst] -> Ti Subst
combineSubs = unify . map1st TyMeta
            . concatMap (magic . Map.toAscList)

--------- Substitution orientation bias

-- The "magic" switch controls how the algorithm orients type
-- substitutions, which in turn affects how it picks type parameters and
-- type indices by breaking the symmetry in scrutinee and pattern types.
-- With magic turned off (i.e., magic = id), the algorithm exhibits the
-- bias that type indices come before type parameters.  With magic
-- turned on (i.e., magic = reverse), the algorithm exhibits the
-- opposite bias: type parameters come before type indices.  The magic
-- does not formally change the expressiveness of Algorithm P, but it
-- does seem to fit currently programming practices better (and it
-- allows the implementation to infer expected types for both runState_o
-- and fdComp1).

magic = reverse

