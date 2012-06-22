-- Time-stamp: <2010-05-05 15:07:22 cklin>

module Inference (inferTop) where

import Control.Monad
import Data.List ((\\), intersect, nubBy, union)
import qualified Data.Map as Map

import Types
import Common
import Monad
import Substitution
import Branches

--------- Type instantiation and generalization

instantiate :: EndoTi Type
instantiate t =
    do let btvx = freeType t
       inst <- liftM (zip btvx) (freshenIndex btvx)
       return (instType (toMap inst) t)

names :: [String]
names = expand ("" : names) (map (:[]) ['a'..'z'])
    where expand ax bx = [ a ++ b | a <- ax, b <- bx ]

generalize :: [Int] -> Endo Type
generalize outer t = zonk (toMap gen) t where
    gen = zip (metaType t \\ outer) (map TyVar names)

--------- Constructor and variable type lookup functions

lookupCons :: ConsE -> String -> Ti Type
lookupCons consE dc =
    case Map.lookup dc consE of
      Nothing -> fail ("Unknown constructor " ++ dc)
      Just (ConsTy t) -> instantiate t

lookupVar :: VarE -> Ident -> Ti Type
lookupVar varE v =
    case Map.lookup v varE of
      Nothing -> fail ("Unknown variable " ++ v)
      Just (VarTy t) -> instantiate t

--------- Type inference for top-level definitions

inferTop :: ConsE -> Term -> Ti Type
inferTop consE e =
    do let vx = ["+", "undefined"]
           tx = [plusType, botType]
           env = (consE, vars vx tx)
       (_, _, t) <- inferType env e
       return (generalize [] t)

--------- Main type inference algorithm

type Env = (ConsE, VarE)
type Result = (Subst, Reach, Type)

var :: Ident -> Type -> VarE
var x t = Map.singleton x (VarTy t)

vars :: [Ident] -> [Type] -> VarE
vars xs = Map.map VarTy . toMap . zip xs

zonkE :: Subst -> Endo VarE
zonkE = mapVarE . zonk

simple :: Type -> Result
simple t = (zeroSub, trueR, t)

inferType :: Env -> Term -> Ti Result
inferType (consE, varE) = infer where
    showEnv = mapM_ (mesg . showLocal) . Map.assocs
    metaE = metaVarE varE

    -- Type inference in an extended variable type environment.  I use
    -- the left-bias property of Map.union to implement shadowing.

    inferVar newE =
        inferType (consE, Map.union newE varE)

    -- This wrapper function applies the inferred substitution to the
    -- reachability constraint, and check that the refined reachability
    -- constraint is satisfiable.

    infer e =
        do (sub, r, t) <- infer' e
           trimmed <- checkR (metaType t ++ metaE) (zonkR sub r)
           return (restrictSub metaE sub, trimmed, t)

    infer' (Int _) = return (simple intType)
    infer' (Con c) = liftM simple (lookupCons consE c)
    infer' (Var v) = liftM simple (lookupVar varE v)

    -- This type inference algorithm for function application is taken
    -- from the paper "On the Unification of Substitutions in Type
    -- Inference" by Bruce J. McAdam.

    infer' (App f e) =
        do (sub_f, r_f, t_f) <- infer f
           (sub_e, r_e, t_e) <- infer e
           t_r <- newMetaTv
           sub_r <- unify2 t_f (arrType t_e t_r)
           sub <- combineSubs [sub_f, sub_e, sub_r]
           return (sub, union r_f r_e, zonk sub t_r)

    infer' (Lam u e) =
        do t_u <- newMetaTv
           (sub, r, t_e) <- inferVar (var u t_u) e
           return (sub, r, arrType (zonk sub t_u) t_e)

    infer' (Let l e) =
        do (sub_l, r_l, vE) <- inferLocal l
           showEnv vE
           (sub_e, r_e, t_e) <- inferVar vE e
           sub <- combineSub sub_l sub_e
           return (sub, union r_l r_e, zonk sub t_e)

    infer' (Case e w) =
        do (sub_e, r_e, t_e) <- infer e
           (sub_wx, r_w, i_b, t_s) <- inferBranches w

           -- Combine the inferred type of the case scrutinee with the
           -- requirement from the pattern-matching branches.  The flip
           -- in the computation for sub_branches is important to avoid
           -- type variable renaming from scrutinee type variables.

           unifier <- unify2 t_e t_s
           let scrutinee = zonk unifier t_s
           sub_ctx <- combineSub sub_e unifier
           sub_branches <- mapM (flip combineSub sub_ctx) sub_wx

           -- Fill in the empty (unconstrained) positions in the branch
           -- type substitutions.

           let dom     = unionMap domSub sub_branches
               indices = metaType scrutinee `intersect` dom
               params  = metaType scrutinee \\ indices
               i_body  = i_b : metaE
               labels  = indices `union` i_body
           map_wx <- mapM (divertSub labels) sub_branches

           -- Compute how GADT type refinement in each branch affects
           -- the scrutinee and the environment / body type variables.

           let indexing = map (branchTypes map_wx) indices
               branches = map (branchTypes map_wx) i_body

           -- Compute a single type substitution to represent the
           -- varying type assumptions inferred from each
           -- pattern-matching branch.  This is the part of the
           -- algorithm that takes advantage of type indexing.

           (match, unmatched) <- reconcile params (indexing, branches)
           tie <- (combineSubs <=< mapM equalize) unmatched

           sub <- combineSub match tie
           return (sub, union r_e r_w, zonkIndex sub i_b)

    -- Infer the types of pattern matching branches.  This function
    -- computes a single scrutinee type for all branches, but it does
    -- not attempt to resolve differences in environment and branch body
    -- types (which may require using type indexing).

    inferBranches :: [Branch] -> Ti ([Subst], Reach, Int, Type)
    inferBranches branches =
        do i_body <- newMetaIndex
           inferred <- mapM (inferBranch i_body) branches
           let (sub, rx, scrutinees) = unzip3 inferred

           unifier <- scrutineeType sub scrutinees

           let r = zonkR unifier (unions rx)
               scrutinee = zonk unifier (head scrutinees)
           unified_sub <- mapM (flip combineSub unifier) sub
           return (unified_sub, r, i_body, scrutinee)

    -- Infer the type of a single pattern-matching branch.  The integer
    -- i represents a placeholder meta type variable for the branch body
    -- type; see comment at the end of the function for the meaning of
    -- the returned substitution.

    inferBranch :: Int -> Branch -> Ti (Subst, Reach, Type)
    inferBranch i (p, e) =
        do (newE, pattern) <- patternType p
           (sub_e, r_e, t_e) <- inferVar newE e

           -- To avoid false positives in recognizing generalized
           -- existential types, we trim the inferred type substitution
           -- sub_e to retain only the mappings that are relevant.

           let i_e = metaType t_e
               i_local = metaVarE newE
               i_env = unions [metaE, i_local, i_e]
               i_pat = metaType pattern
               eta = shaveSub i_env sub_e
               eta_local = shaveSub i_pat eta

           -- Compute the set v_esc of instantiated or escaped pattern
           -- type variables and check for existential type violations.

           let i_ext = intersect (metaSub eta `union` i_e) i_local
           unless (i_ext `subset` i_pat)
                  (fail "Existential type escape or instantiation")

           -- Compute a most general scrutinee type by transcribing
           -- instantiated type variables from the pattern type to the
           -- scrutinee type.  Use the computed scrutinee type to update
           -- the reachability constraint for the branch.

           copy <- transcribe (metaSub eta_local) pattern
           scrutinee <- if metaP copy
                        then freshenTyCon pattern
                        else return (zonk eta copy)
           let r = attachR (scrutinee, pattern) r_e

           -- The ordering of "pattern" and "scrutinee" matters: placing
           -- the pattern type first avoids generating trivial renaming
           -- from scrutinee type variables to pattern type variables.
           -- Such renaming makes the type inference algorithm mistake
           -- ADT type variables for GADT type variables and could cause
           -- type inference failure for some ADT case expressions.

           refinement <- unify2 pattern scrutinee

           -- The substitution sub combines two different kinds of type
           -- information into one.  With domain restricted to the
           -- scrutinee type variables, it represents GADT type
           -- refinements for the branch (sub_ps).  With domain
           -- restricted to the outer environment type variables, it
           -- represents the assumptions that the branch makes on the
           -- environment (eta).  With domain restricted to i, it
           -- represents the type of the branch body.

           sub <- combineSubs [refinement, eta, oneSub i t_e]
           return (sub, r, scrutinee)

    -- Given a pattern, compute a pattern type and construct a
    -- corresponding type environment fragment for the pattern-bound
    -- variables.

    patternType :: Pat -> Ti (VarE, Type)
    patternType (PatInt _) = return (Map.empty, intType)
    patternType (PatCon c xs) =
        do (t_ax, t_p) <- liftM spine (lookupCons consE c)
           unless (length t_ax == length xs)
                  (fail "Data constructor arity mismatch")
           return (vars xs t_ax, t_p)

    -- Infer polymorphic types for recursive local let definitions using
    -- Mycroft's extension to Algorithm W (described in "Polymorphic
    -- Type Schemes and Recursive Functions", 1984).  The function
    -- returns, among other things, a type environment fragment for
    -- local definitions.

    inferLocal :: [(Ident, Term)] -> Ti (Subst, Reach, VarE)
    inferLocal locals = mycroft limit zeroSub fullpoly where
        (ux, ex) = unzip locals
        fullpoly = repeat (TyVar "a")

        -- Since Mycroft's fix rule is only a semi-algorithm, we must
        -- enforce termination by limiting the number of iterations.
        -- The limit defined here is fairly conservative; a limit of 3
        -- is sufficient for all the included examples.

        limit = 20

        mycroft 0 _ _ = fail "Mycroft iteration limit reached"
        mycroft n init types =
            do result <- arrestTi (refinePoly init types)
               case result of
                 (w, Nothing) -> do { replay w ; die }
                 (w, Just (sub, r, sigma)) ->
                     if sigma /= map (zonk sub) types
                     then mycroft (n-1) sub sigma
                     else do replay w
                             return (sub, r, vars ux sigma)

        -- Infer polymorphic types for local definitions under a
        -- substitution and a polymorphic type environment.  Unlike in
        -- the Hindley-Milner type inference algorithm, we do not unify
        -- the types in the environment and the inferred types of the
        -- local definitions.

        refinePoly sub_init types_init =
            do let env_init = vars ux types_init
               inferred <- mapM (inferVar env_init) ex
               let (subs, rx, tx) = unzip3 inferred
               sub <- combineSubs (sub_init : subs)
               let outer = metaVarE (zonkE sub varE)
                   types_new = map (zonk sub) tx
                   sigma_new = map (generalize outer) types_new
               return (sub, unions rx, sigma_new)

