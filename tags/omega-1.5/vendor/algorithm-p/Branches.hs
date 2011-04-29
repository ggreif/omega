-- Time-stamp: <2010-05-12 14:23:36 cklin>

module Branches where

import Control.Monad (liftM, unless)
import Data.List ((\\), transpose)
import Data.Maybe (isJust, mapMaybe)
import qualified Data.Map as Map

import Types
import Common
import Monad
import Substitution

--------- Branch type manipulation functions

-- Create a minimal (i.e., most general) type that has all the specified
-- meta type variables in the same position as the input type.

transcribe :: [Int] -> EndoTi Type
transcribe keep = render where
    render t@(TyMeta i) =
        if i `elem` keep
        then return t else newMetaTv
    render (TyCon tc ax) =
        if metaTypes ax `overlaps` keep
        then liftM (TyCon tc) (mapM render ax)
        else newMetaTv
    render (TyVar _) =
        bug "Bounded type variable in transcribe"
    render (TySkol _) =
        bug "Skolem type in transcribe"

-- Compute a scrutinee type from the branch scrutinee type templates and
-- type indexing substitutions.  We use the extractTc function to
-- specialize the scrutinee type, which ensures that GADT type
-- refinements for each scrutinee type variable do not all have the same
-- top-level type constructor.

scrutineeType :: [Subst] -> [Type] -> Ti Subst
scrutineeType sub_branch scrutinees =
    do unifier <- unifyTypes scrutinees
       sub <- reach (mapM (combineSub unifier) sub_branch)
       let indices = metaType (zonk unifier $ head scrutinees)
           indexing = map (branchTypes sub) indices
       extract <- liftM fst (extractTc indexing)
       return (compoSub extract unifier)

-- The Split type describes how a meta type variable (represented by the
-- Int value) appears in each pattern-matching branch, and the
-- branchTypes function is its factory function.

type Split = (Int, [Type])

branchTypes :: [Subst] -> Int -> Split
branchTypes sub i = (i, indexed) where
    indexed = map (flip zonkIndex i) sub

zonkSplit :: Subst -> Endo Split
zonkSplit sub (i, tx) = (i, map (zonk sub) tx)

-- The extractTc function extracts common top-level type constructors in
-- the branch types and apply them to the corresponding type variables.
-- extractTc [(x, [Int])] == ([Int/x], [])
-- extractTc [(x, [T Int, T Bool])] == ([T y/x], [(y, [Int, Bool])])
-- extractTc [(x, [Bool, T Int])] == ([], [(x, [Bool, T Int])])

extractTc :: [Split] -> Ti (Subst, [Split])
extractTc [] = return (zeroSub, [])
extractTc ((i, tx) : ux) =
    case deCons tx of
      Nothing ->
          do (sub, vx) <- extractTc ux
             return (sub, (i, tx) : ux)
      Just (tc, ax) ->
          do ix <- freshenIndex (head ax)
             let newTc = TyCon tc (map TyMeta ix)
                 uax = zip ix (transpose ax)
             (sub, vx) <- extractTc (uax ++ ux)
             return (compoSub sub (oneSub i newTc), vx)

-- The matchTc function is similar to extractTc, except that it requires
-- only that the branch types be coercible to a single type constructor.
-- The function reports failure if the condition is not met.

matchTc :: Split -> Ti (Subst, [Split])
matchTc (i, tx) =
    case deCons (filter consP tx) of
      Nothing -> fail "Cannot match type constructors"
      Just (tc, ax) ->
          do let template = TyCon tc (head ax)
             imprint <- mapM (imprintTc template) tx
             let imprinted = zipWith zonk imprint tx
             (inst, vx) <- extractTc [(i, imprinted)]
             sub <- combineSubs (inst : imprint)
             return (sub, vx)

-- Skolemize all occurrences of pattern type variables to prevent the
-- type indexing process from introducing unintentional instantiations
-- (which can create new generalized existential types == BAD).

freeze :: [Int] -> Endo ([Split], [Split])
freeze excl (indexing, env) = (skol indexing, skol env) where
    pattern_v = unionMap (metaTypes . snd) indexing \\ excl
    skol = map (zonkSplit (skolemize pattern_v))

equalize :: Split -> Ti Subst
equalize (i, tx) =
    if null (skolTypes tx)
    then attemptTi [unifyTypes (TyMeta i : tx)]
         (fail "Cannot reconcile branch body types")
    else fail "A pattern type escapes in equalize"

-- Reconcile the mapping from environment meta type variables to branch
-- types into a single type substitution with the help of type indexing.

reconcile :: [Int] -> ([Split], [Split]) -> Ti (Subst, [Split])
reconcile params = driver zeroSub . freeze params where

    -- The driver function repeatedly invokes the matcher until it
    -- reaches a fixed-point (at which point the matcher cannot make
    -- more progress), and then it returns the combined matching along
    -- with the unsolved branch types.

    driver prev (indexing, variety) =
        do result <- mapM matcher variety
           sub <- combineSubs (map fst result)
           let update = map (zonkSplit sub)
               unsolved = update (concatMap snd result)
           combined <- combineSub prev sub
           let param_inst = map (zonkIndex combined) params
           unless (null (skolTypes param_inst))
                  (fail "A pattern type escapes in reconcile")
           if nullSub sub
              then return (combined, unsolved)
              else driver combined (update indexing, unsolved)

    -- The matcher function tries to reconcile pattern types that are
    -- not unifiable by either matching them to a unique type index or
    -- matching (and unwrapping) a top-level type constructor.

     where
      matcher variety@(_, tx) =
        if isJust (unifiableTypes tx) && null (skolTypes tx)
        then return (zeroSub, [variety])
        else attemptTi [matchIndex variety, matchTc variety]
                       (return (zeroSub, [variety]))

      matchIndex (i, tx) =
        let runSnd f (x, y) = do { z <- f y ; return (x, z) }
            couple = runSnd (unifiable . zip tx)
        in case mapMaybe couple indexing of
             [(k, sub)] -> let index = oneSub i (TyMeta k)
                           in return (compoSub index sub, [])
             _ -> fail "Cannot find unique matching type index"

--------- Branch reachability constraints

-- We use Type2 to represent the type-level (potential) reachability of
-- a branch.  The first component is the scrutinee type, and the second
-- component is the pattern type.  The Reach type represents the
-- reachability constraints in disjunctive normal form: nested patterns
-- are linked by conjunctions, and non-nested patterns (whether in the
-- same case expression or not) are linked by disjunctions.

type Reach = [[Type2]]

-- A trivial reachability constraint is the disjunction of an empty
-- conjunction (True), which differs from an empty disjunction (False).

trueR :: Reach
trueR = [[]]

-- Since inferred type substitutions should never affect the pattern
-- types, the zonkR function applies the substitution only to the
-- scrutinee types (first component of the pair).

zonkR :: Subst -> Endo Reach
zonkR = map . map1st . zonk

-- Add a nested pattern to a reachability constraint.

attachR :: Type2 -> Endo Reach
attachR r = map (r:)

-- Check the satisfiability of a reachability constraint: type equations
-- in each conjunction must be simultaneously unifiable.

checkR :: [Int] -> EndoTi Reach
checkR ix r =
    do reach (mapM_ unify r)
       return r

reach :: Endo (Ti a)
reach m = attemptTi [m] (fail "A branch is unreachable")

