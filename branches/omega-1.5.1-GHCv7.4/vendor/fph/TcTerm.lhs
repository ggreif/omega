\begin{code}
module TcTerm where

import BasicTypes
import BasicTypesUtils
import TcMonad
import TcUnify
import List( (\\) )
import Data.IORef 
import Text.PrettyPrint.HughesPJ

-----------------------------------------
--    Utilities                        --
-----------------------------------------

skolemizeApplicable :: Term -> Bool 
-- checks whether the term is an e-term
skolemizeApplicable (Lam _ _) = True 
skolemizeApplicable _         = False 

isMetaTv :: Type -> Bool 
isMetaTv (MetaTv _) = True 
isMetaTv _ = False 

------------------------------------------
--      The top-level wrapper           --
------------------------------------------
typecheck :: Term -> Tc Sigma 
typecheck e = inferSigma e 

----------------------------------------------------------------
--   The expected type                                        --
----------------------------------------------------------------
data Expected a = Infer (IORef a) | Check a


----------------------------------------------------------------
-- Scheme generalization                                      -- 
----------------------------------------------------------------
generalize :: Type -> Tc Scheme 
generalize ty 
  = do { nty <- normalize ty 
       ; env_tys <- getEnvTypes 
       ; env_tvs <- getMetaTyVars env_tys 
       ; res_tvs <- getMetaTyVars [nty]
       ; let qvs = res_tvs \\ env_tvs 
       ; return (Scheme qvs nty)
       }

quantifyAndMono :: Type -> Tc Type 
quantifyAndMono ty 
  = do { tym <- instMono ty 
       ; z_ty <- zonkType tym
       ; env_tys <- getEnvTypes 
       ; env_tvs <- getMetaTyVars env_tys 
       ; res_tvs <- getMetaTyVars [z_ty] 
       ; let forall_tvs = res_tvs \\ env_tvs 
       ; quantify forall_tvs z_ty
       }

instFun :: Type -> Tc (Type,Type) 
instFun (Fun s1 s2) = return (s1,s2) 
instFun ty@(MetaTv _) 
  = do { nty <- normalize ty 
       ; ty1 <- newTyVarTy 
       ; ty2 <- newTyVarTy 
       ; eqCheck nty (Fun ty1 ty2) 
       ; return (ty1,ty2) }
instFun ty 
  = failTc $ vcat [ text "Cannot arrow-unify type", 
                    nest 2 (ppr ty)
                  ]

instMono :: Type -> Tc Type 
instMono ty@(MetaTv _) 
  = do { nty <- normalize ty 
       ; mkMono True nty 
       ; return nty
       }
instMono ty 
  = do { mkMono False ty 
       ; return ty }


---------------------------------------------------------------
--  Instantiation/Subsumption                                --
---------------------------------------------------------------
instSigma :: Sigma -> Expected Sigma -> Tc ()
instSigma ty1 (Check ty2) 
  = do { sch1 <- generalize ty1
       ; extSubsCheck sch1 ty2 
       }
instSigma ty1 (Infer ref) 
  = instantiate ty1 >>= writeTcRef ref


---------------------------------------------------------------
-- inferSigma and checkSigma                                 --
---------------------------------------------------------------

checkSigma :: Term -> Sigma -> Tc ()

-- rule out pathological case: this way we can never have 
-- checkRho called on a function with a single box

checkSigma e rty@(MetaTv _) 
  = do { ty <- inferRho e
--     ; debugTc $ text "checkSigma for term:" <+> ppr e 
--     ; debugTc $ text "inferred type: " <+> ppr ty
       ; sch <- generalize ty 
       ; extSubsCheck sch rty } 

checkSigma e ty
  = do { (sks,rho) <- skolemise ty 
       ; checkRho e rho 
       ; env_tys <- getEnvTypes 
       ; esc_tvs <- getFreeTyVars (ty : env_tys) 
       ; let bad_tvs = filter (`elem`  esc_tvs) sks
       ; check (null bad_tvs) 
               (text "Type not polymorphic enough!") }

inferSigma :: Term -> Tc Sigma 
-- Returns a monomorphised type
inferSigma e = inferRho e >>= quantifyAndMono 

----------------------------------------------------------
-- inferRho, checkRho                                   --
----------------------------------------------------------                   

checkRho :: Term -> Rho -> Tc ()
checkRho expr ty = tcRho expr (Check ty) 

inferRho :: Term -> Tc Rho
inferRho expr 
  = do { ref <- newTcRef (error "inferRho: empty result")
       ; tcRho expr (Infer ref)
       ; readTcRef ref }

tcRho :: Term -> Expected Rho -> Tc () 
tcRho (Lit _) exp_ty 
  = instSigma intType exp_ty 
tcRho (Var v) exp_ty 
  = do { v_sigma <- lookupAtom v 
       ; instSigma v_sigma exp_ty } 
tcRho (Con c) exp_ty 
  = do { sigma <- lookupAtom c 
       ; instSigma sigma exp_ty } 
tcRho (App e1 e2) exp_ty 
  = do { fun_ty <- inferRho e1 
       ; (arg_ty, res_ty) <- instFun fun_ty 
       ; checkSigma e2 arg_ty 
       ; instSigma res_ty exp_ty } 
tcRho (Let x u e) exp_ty 
  = do { xty <- inferSigma u 
       ; extendTermEnv x xty (tcRho e exp_ty) }
tcRho (AnnLet x ty u e) exp_ty 
  = do { checkSigma (Ann u ty) ty
       ; extendTermEnv x ty (tcRho e exp_ty) }

-- liberal annotation rule implementation 
tcRho (Ann e annty) exp_ty 
  = do { checkSigma e annty 
       ; instSigma annty exp_ty }

-- tcRho ea@(Ann e annty) exp_ty
--   = do { ty <- inferRho e
--          -- liberal (constrained) subsumption  
--        ; debugTc $ text "Calling annsubs for expression:" <+> ppr ea 
--        ; genAndSubs ty annty
--        ; instSigma annty exp_ty }


tcRho (Lam (PVar x) e) (Infer ref) 
  = do { var_ty <- newTyVarTy 
       ; mkMono False var_ty 
       ; body_ty <- extendTermEnv x var_ty (inferRho e) 
       ; body_ret <- instMono body_ty 
       ; qty <- quantifyAndMono (var_ty --> body_ret)
       ; final_ty <- instantiate qty 
       ; writeTcRef ref final_ty }


tcRho (Lam (PVar x) e) (Check (Fun s1 s2)) 
  = do { 
         mkMono False s1 
       ; extendTermEnv x s1 (checkSigma e s2) }
tcRho (Lam (PAnn (PVar x) annty) e) (Check (Fun s1 s2))
  = do { eqCheck s1 annty 
       ; extendTermEnv x annty (checkSigma e s2) } 
tcRho (Lam (PAnn (PVar x) annty) e) (Infer ref) 
  = do { ret_ty <- extendTermEnv x annty (inferRho e) 
       ; mret_ty <- instMono ret_ty 
       ; qty <- quantifyAndMono (annty --> mret_ty) 
       ; final_ty <- instantiate qty 
       ; writeTcRef ref final_ty }

tcRho (Lam _ _) _ 
  = failTc $ text "Lambda abstractions with complex patterns not implemented!"
tcRho (Case _ _) _
  = failTc $ text "Case expression typechecking not implemented!"

\end{code}
