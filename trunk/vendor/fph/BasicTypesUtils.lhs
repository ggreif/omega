\begin{code}
module BasicTypesUtils where 

-- This module defines various utilities on BasicTypes, 
-- such as substitutions, free variable collection, pretty 
-- printing. 

import Text.PrettyPrint.HughesPJ 
import Maybe ( fromMaybe ) 

import BasicTypes


tyVarName :: TyVar -> String
tyVarName (BoundTv n)    = n
tyVarName (SkolemTv n _) = n

-- Replace the specified quantified type variables by 
-- given meta-type variables. In the case of meta-variable
-- we do not perform any substitution, because of the invariant
-- that no meta-variable may contain any quantified variable. 

substTy :: [TyVar] -> [Type] -> Type -> Type
substTy tvs tys ty = subst_ty (tvs `zip` tys) ty

subst_ty :: Env -> Type -> Type
subst_ty env (Fun arg res)   = Fun (subst_ty env arg) (subst_ty env res)
subst_ty env (TyVar n)       = fromMaybe (TyVar n) (lookup n env)
subst_ty _   (MetaTv tv)     = MetaTv tv   
subst_ty env (TyCon tc tys)  = TyCon tc (map (subst_ty env) tys)
subst_ty env (ForAll ns tau) = ForAll ns (subst_ty env' tau)
  where env' = [(n,ty') | (n,ty') <- env, not (n `elem` ns)]


-- split a monotype to its components 
splitCType :: Rho -> ([Sigma],Maybe (Name,[Sigma])) 
splitCType (Fun t1 t2) = (t1:t2args,x) 
  where (t2args,x) = splitCType t2
splitCType (TyCon n taus) = ([],Just (n,taus)) 
splitCType (TyVar _)      = ([],Nothing)


 -----------------------------------
 --      Pretty printing class   -- 
 -----------------------------------

class Outputable a where
  ppr :: a -> Doc

docToString :: Doc -> String
docToString = render

dcolon, dot :: Doc
dcolon = text "::"
dot    = char '.'


-- pretty print your terms 
instance Outputable Term where
   ppr (Var n)       = pprName n
   ppr (Con n)       = pprName n 
   ppr (Lit i)       = int i
   ppr (App e1 e2)   = pprApp (App e1 e2)
   
   ppr (Lam p t)     = sep [char '\\' <> ppr p <> text ".", ppr t] 
   ppr (Let v rhs b) = vcat [text "let" <+> (pprName v <+> equals <+> ppr rhs),
                             text "in" <+> ppr b]
   ppr (AnnLet v ty rhs b) = vcat [text "let" <+> (vcat [pprName v <+> text "::" <+> ppr ty, 
                                                   pprName v <+> equals <+> ppr rhs]), 
                                   text "in" <+> ppr b]

   ppr (Ann e sigma) = pprParendTerm e <+> dcolon <+> pprParendType sigma
   ppr (Case e alts) = vcat[ hsep [text "case", ppr e, text "of"]
                           , vcat (map (\(p,t) -> nest 2 $ hsep [ppr p, text "->", ppr t]) alts)]

instance Outputable Pattern where 
   ppr (PAny) = text "_" 
   ppr (PVar n) = pprName n 
   ppr (PCon n plist) = hsep [ text "(", pprName n, rest <> text ")"]
      where rest = foldr (\p r -> hsep[ppr p,r]) empty plist 
   ppr (PAnn p tau) = text "(" <+> ppr p <+> dcolon <+> pprParendType tau <+> text ")" 

pprParendTerm :: Term -> Doc
pprParendTerm e | atomicTerm e = ppr e
                | otherwise    = parens (ppr e)

pprApp :: Term -> Doc
pprApp e = go e []
  where
    go (App e1 e2) es = go e1 (e2:es)
    go e' es           = pprParendTerm e' <+> sep (map pprParendTerm es)
pprName :: Name -> Doc
pprName n = text n

-------------- Pretty-printing types ---------------------

instance Outputable Type where
    ppr ty = pprType topPrec ty

instance Outputable MetaTv where
    ppr (Meta u _) = text "$" <> int u

instance Outputable TyVar where
    ppr (BoundTv n)    = text n
    ppr (SkolemTv n u) = text n <+> int u


type Precedence = Int
topPrec, arrPrec, tcPrec, atomicPrec :: Precedence
topPrec    = 0  -- Top-level precedence
arrPrec    = 1  -- Precedence of (a->b)
tcPrec     = 2  -- Precedence of (T a b)
atomicPrec = 3  -- Precedence of t

precType :: Type -> Precedence
precType (ForAll _ _)  = topPrec
precType (Fun _ _)     = arrPrec
precType (TyCon _ [])  = atomicPrec 
precType (TyCon _ _)   = tcPrec 
precType _             = atomicPrec   

pprParendType :: Type -> Doc
pprParendType ty = pprType tcPrec ty


pprType :: Precedence -> Type -> Doc
-- Print with parens if precedence arg > precedence of type itself
pprType p ty | p >= precType ty = parens (ppr_type ty)
             | otherwise        = ppr_type ty

ppr_type :: Type -> Doc         -- No parens
ppr_type (ForAll ns ty) = sep [text "forall" <+> 
                                   hsep (map ppr ns) <> dot, 
                                ppr ty]
ppr_type (Fun arg res)  = sep [pprType arrPrec arg <+> text "->", 
                                pprType (arrPrec-1) res]
ppr_type (TyCon c tys)  = pprName c <+> foldr (\ty r -> hsep[pprType tcPrec ty,r]) empty tys
ppr_type (TyVar n)      = ppr n
ppr_type (MetaTv tv)    = ppr tv


instance Outputable Ctor where 
  ppr (Ctor n sigma) = sep [pprName n <+> text "::" <+> ppr sigma] 

instance Outputable Decl where 
  ppr (Data n vars ctrs) = 
      hsep [text "data", pprName n, 
           foldr (\v r -> hsep[pprName v, r]) empty vars, 
           text "where", 
           vcat (map (nest 2.ppr) ctrs)]
  ppr (AnnDef n sigma) = 
      sep [pprName n <+> text "::" <+> ppr sigma]
  ppr (Def n plist def) = 
      hsep [pprName n <+> 
             (foldr (\p r -> hsep[ppr p,r]) empty plist) <+> text "=", 
            ppr def] 


\end{code}
