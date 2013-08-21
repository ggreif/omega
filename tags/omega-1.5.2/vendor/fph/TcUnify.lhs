\begin{code}
module TcUnify where 

import BasicTypes
import BasicTypesUtils 
import TcMonad

import Text.PrettyPrint.HughesPJ
import List( (\\) )
import Monad ( zipWithM_ ) 


---------------------------------------------------------------------
-- Equivalence and subsumption checking 
---------------------------------------------------------------------

eqCheck :: Sigma -> Sigma -> Tc () 
eqCheck (TyVar tv1) (TyVar tv2) | tv1 == tv2 = return () 
eqCheck (MetaTv tv) ty = updateRigid tv ty 
eqCheck ty (MetaTv tv) = updateRigid tv ty 
eqCheck (Fun a1 r1) (Fun a2 r2) = eqCheck a1 a2 >> eqCheck r1 r2 
eqCheck (TyCon tc1 tys1) (TyCon tc2 tys2) 
  | tc1 == tc2 = zipWithM_ eqCheck tys1 tys2
eqCheck (ForAll avs r1) (ForAll bvs r2) 
  | length avs == length bvs 
  = do { (sks, r2s) <- skolemise (ForAll bvs r2) 
       ; mvs <- mapM (\_ -> newMetaTyVar) avs 
       ; let r1s = substTy avs (map MetaTv mvs) r1 
       ; eqCheck r1s r2s 
       -- make sure skolems did not escape 
       ; tvs <- freeTyVars [(ForAll avs r1),(ForAll bvs r2)] 
       ; let bad_tvs = filter (`elem` sks) tvs 
       ; check (null bad_tvs) 
             (vcat [text "Equivalence checking failed for types:", 
                    nest 2 (ppr (ForAll avs r1)), 
                    text "and", 
                    nest 2 (ppr (ForAll bvs r2))])
       -- no need to check that two types have their skolems in 1-1 mapping, 
       -- they both come from user type annotations---if user gave the wrong type, oh well ... 
       }
eqCheck ty1 ty2 
  = failTc $ text "Equivalence checking:" <+> ppr ty1 <+> text " ~ " <+> ppr ty2 <+> text "failed!"


extSubsCheck :: Scheme -> Type -> Tc () 
extSubsCheck sch (MetaTv tv) = updateFlexi tv sch
extSubsCheck (Scheme vrs r1) s2
  = do { pre_meta_tvs <- metaTvs [r1,s2]
       ; let meta_tvs = pre_meta_tvs \\ vrs 
       ; (skol_tvs, r2) <- skolemise s2
       ; eqCheck r1 r2 
       -- escaped variables = those that escaped in the original 
       -- unification variables of the scheme and the required type 
       ; esc_tvs <- getFreeTyVars (map MetaTv meta_tvs) 
       ; let bad_tvs = filter (`elem` esc_tvs) skol_tvs 
       -- todo: following error message needs cleaning-up
       ; check (null bad_tvs) 
               (vcat [text "Subsumption check failed, when checking a scheme against type", 
                      nest 2 (ppr s2)])
       }


------------------------------------------------------------------------------------------------
-- updateRigid and updateFlexi                                                                --
------------------------------------------------------------------------------------------------

updateRigid :: MetaTv -> Type -> Tc () 
-- (updateRigid tv ty) 
--	adds an equality bound to tv; i.e. ty = tv
updateRigid tv ty 
  = case ty of 
      -- if ty is the same variable, do nothing 
      MetaTv tv0 | tv == tv0 -> return () 
      -- if ty is a different variable
      MetaTv tv0 -> 
          do { (TyInfo _ bound0) <- readTv tv0
             ; case bound0 of 
                 -- ty = (a := ty0)   zonk through ty0 
                 Rigid ty0 -> updateRigid tv ty0
                 -- ty = (a >= b)     b must be monomorphic hence zonk through as if it were (a := b)!
                 Flexi (Scheme [] (MetaTv tv1)) -> updateRigid tv (MetaTv tv1)
                 -- in all other cases 
                 -- ty = (a >= sigma) \/ (a unbound) do the occur check and update the bound
                 _ -> doUpdateR tv ty
             }
    -- if ty is not a variable at all! 
      _ -> doUpdateR tv ty 

 where doUpdateR :: MetaTv -> Type -> Tc () 
       doUpdateR v ty0 
        = do { meta_tvs <- getMetaTyVars [ty0] 
             ; check (not (v `elem` meta_tvs)) (text "Occur check error!") 
             ; (TyInfo f bnd) <- readTv v 
             ; case (f,bnd) of 
                 (True,None)  -> mkMono True ty0 >> writeTv v (TyInfo True (Rigid ty0)) 
                 (_,None)     -> writeTv v (TyInfo f (Rigid ty0)) 
                 (_,Flexi sy) -> do { extSubsCheck sy ty0 
                                    ; writeTv v (TyInfo f (Rigid ty0)) } 
                 (_,Rigid sy) -> eqCheck sy ty0 
             }

updateFlexi :: MetaTv -> Scheme -> Tc () 
-- updateFlexi tv ty: 
--	adds a instantiation bound to tv; i.e. ty <= tv
-- precondition: sch is monomorphized + metaTvZonked
updateFlexi tv sch 
  = case sch of 
      -- if you see a variable, it must be monomorphic hence, updateRigid 
      Scheme [] ty@(MetaTv _) -> updateRigid tv ty
      _ -> doUpdateF tv sch 
 where doUpdateF :: MetaTv -> Scheme -> Tc () 
       doUpdateF v (Scheme vrs ty) 
        =  do { pre_meta_tvs <- getMetaTyVars [ty] 
              ; let meta_tvs = pre_meta_tvs \\ vrs 
              ; check (not $ v `elem` meta_tvs) (text "Occur check error!") 
              ; (TyInfo f bnd) <- readTv v 
              ; case (f,bnd) of 
                  (True,None) -> 
                      do { writeTv v (TyInfo f (Flexi sch)) 
                         ; mkMono True (MetaTv v) }
                  (_,None) -> writeTv v (TyInfo f (Flexi sch)) 
                  (_,Rigid sy)   -> extSubsCheck sch sy
                  (_,Flexi sch0) -> do { schj <- extJoin sch sch0
                                      ; writeTv v (TyInfo f (Flexi schj)) }
              }


extJoin :: Scheme -> Scheme -> Tc Scheme 
-- returns the join of the two input types. 
-- assumes that sch1 sch2 are monomorphized + metaTvZonked
extJoin (Scheme [tv1] (MetaTv tv2)) sch2 | (tv1 == tv2) = return sch2 
extJoin sch1 (Scheme [tv1] (MetaTv tv2)) | (tv1 == tv2) = return sch1 
extJoin (Scheme vrs1 ty1) (Scheme vrs2 ty2) 
  = do { pre_meta_tvs <- metaTvs [ty1,ty2]
       ; let meta_tvs = (pre_meta_tvs \\ vrs1) \\ vrs2 
       ; eqCheck ty1 ty2
       ; ty1_fcv <- fcv [ty1] 
       ; let preqvs = filter (`elem` ty1_fcv) vrs1
       ; all_vs <- metaTvs (map MetaTv preqvs) 
       ; non_q  <- metaTvs (map MetaTv meta_tvs) 
       ; let qvs = all_vs \\ non_q
       ; return (Scheme qvs ty1) } 



-- genAndSubs :: Type -> Type -> Tc () 
-- -- cty: constrained type 
-- -- aty: annotation type 
-- genAndSubs cty_in aty 
--  = do {
--       ; (Scheme org_vrs cty) <- zonkMetaTv cty_in 
--       -- pseudo-quantify over all its metavariables not in the environment
--       ; env_tys <- getEnvTypes 
--       ; env_tvs <- getMetaTyVars env_tys 
--       ; res_tvs <- getMetaTyVars [cty]
--       ; let forall_tvs = (res_tvs ++ org_vrs) \\ env_tvs 
--       -- the non-quantified meta-tvs 
--       ; extSubsCheck (Scheme forall_tvs cty) aty 
--       }
      
-- eliminate all single-variable types 
normalize :: Type -> Tc Type 
normalize (MetaTv tv)
  = do { (TyInfo f b) <- readTv tv 
       ; case f of 
           True -> return (MetaTv tv)
           False -> case b of 
                      None -> return (MetaTv tv)
                      Flexi (Scheme _ ty) -> normalize ty
                      Rigid ty -> normalize ty 
       }
normalize ty = instantiate ty


\end{code}