{-# LANGUAGE MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  #-}
module NarrowData where

import System.IO.Unsafe(unsafePerformIO)
import RankN

import SyntaxExt(SynExt(..))
import Bind(Name)
import Auxillary
import Monads

-------------------------------------------------------------------
-- When narrowing we need to partition terms into 4 classes
-- 1) variables, 2) constructors, 3) function calls, 4) predicates
-- To do this we provide the type NS. Terms are composed of
-- Names (of constructors or constants), Variables, and Subterms.
-- We provide projection (Tau -> NS) functions and injection (NS -> Tau)
-- functions. This way we need only write the code once that decides
-- what class a term is in.

data NName
  = NTyCon String (SynExt String) Level PolyKind
  | NTyApp
  | NStar Level
  | NKarr
  | NTyVar Name Kind
  | NSkol Integer String Kind

data NS name var term
  = VarN var
  | FunN name [term]
  | ConN name [term]
  | RelN (Rel term)

data Rel term
  = EqR (term,term)
  | AndR [Rel term]

data Prob t
  = TermP t
  | EqP (t,t)
  | AndP [Prob t]

type Sol = [(Prob Tau,Rel Tau,Unifier2)]
type ST z = (Int,Int,DispInfo z,Bool)
type Un var term = [(var,term)]

-------------------
-- For constucting DefTrees

type Path = [Int]

data DefTree var term
  = Leaf term [var] term term
  | Branchx term Path [DefTree var term]

data Chain var term
  = Root term
  | Next term Path (Chain var term)
  deriving Show
  


-- For encoding Rules and solutions to narrowing problems

data Rule name var term = NarR(name,[([var],[term],term)])

data NResult v t =
    Answers  [(t,Un v t)]
  | Exceeded [(t,Un v t)]

-------------------------------------------------------
-- Projection out of Tau, and injection into NS

project :: Tau -> NS NName TcTv Tau
project x@(TyVar n k) = ConN (NTyVar n k) []
project t | equalP t = RelN(EqR(equalParts t))
project t@(TyApp x y) =
  case rootT t [] of
   Just(sx,lev,nm,k,xs) -> ConN (NTyCon nm sx lev k) xs
   Nothing -> ConN NTyApp [x,y]
project x@(Star n) = ConN (NStar n) []
project (Karr a b) = ConN NKarr [a,b]
project (TyFun s p xs) = FunN (NTyCon s Ox (lv 0) p) xs
project (TcTv (Tv n (Skol s) k)) = ConN (NSkol n s k) []
project (TcTv s) = (VarN s)
project (TySyn s n xy ys t) = project t
project x@(TyEx _) = error ("Can't project anonymous existential types:\n  "++show x)
project (TyCon sx level n k) = ConN (NTyCon n sx level k) []

inject :: NS NName TcTv Tau -> Tau
inject (VarN s) = (TcTv s)
inject (FunN (NTyCon n sx lev k) xs) = TyFun n k xs
inject (ConN (NTyVar n k) []) = TyVar n k
inject (ConN NTyApp [x,y]) = TyApp x y
inject (ConN (NStar n) []) = Star n
inject (ConN NKarr [a,b]) = Karr a b
inject (ConN (NSkol n s k) []) = TcTv (Tv n (Skol s) k)
inject (ConN (NTyCon n sx lev k) xs) = f (TyCon sx lev n k) xs
  where f x [] = x
        f x (y:ys) = f (TyApp x y) ys
inject (RelN (EqR(x,y))) = teq x y

---------------------------------------------------------------------
-- relations (Rel) and Problems (Prob) are type-like

instance Zonk m a => Zonk m (Prob a) where
  zonkG (TermP x) = do { a <- zonkG x; return (TermP a) }
  zonkG (EqP(x,y)) = do { a <- zonkG x; b <- zonkG y; return (EqP(a,b)) }
  zonkG (AndP xs) = do { as <- mapM (zonkG) xs; return (AndP as) }

  tvs (TermP x) = tvs x
  tvs (EqP(x,y)) = binaryLift unionP (tvs x) (tvs y)
  tvs (AndP xs) = tvs xs


instance TypeLike m a => TypeLike m (Prob a) where
  sub env (TermP x) = do { a <- sub env x; return (TermP a) }
  sub env (EqP(x,y)) = do { a <- sub env x; b <- sub env y; return (EqP(a,b)) }
  sub env (AndP xs) = do { as <- mapM (sub env) xs; return (AndP as) }
  
instance Zonk m a => Zonk m (Rel a) where
  zonkG (EqR(x,y)) = do { a <- zonkG x; b <- zonkG y; return (EqR(a,b)) }
  zonkG (AndR xs) = do { as <- mapM (zonkG) xs; return (AndR as) }

  tvs (EqR(x,y)) = binaryLift unionP (tvs x) (tvs y)
  tvs (AndR xs) = tvs xs
  
instance TypeLike m a => TypeLike m (Rel a) where
  sub env (EqR(x,y)) = do { a <- sub env x; b <- sub env y; return (EqR(a,b)) }
  sub env (AndR xs) = do { as <- mapM (sub env) xs; return (AndR as) }

instance Eq NName where
 (NTyCon a sx l1 b) == (NTyCon c tx l2 d) = a==c
 NTyApp       == NTyApp       = True
 (NStar n)    == (NStar m)    = n==m
 NKarr        == NKarr        = True
 (NTyVar n k) == (NTyVar m _) = n==m
 (NSkol n s k) == (NSkol m _ _) = n==m
 _            == _            = False

----------------------------------------------------------------------
-- Code for displaying and printing

dparen x = case project x of
            VarN _ -> Dd x
            FunN _ _ -> Dd x
            ConN _ _ -> Dr[Ds "(",Dd x,Ds ")"]

dProb :: Prob Tau -> DispElem Z
dProb (TermP t) = Dd t
dProb (EqP(x,y)) = Dr [Ds "Equal ",dparen x,Ds " ",dparen y]
dProb (AndP xs) = Dr [Ds "and(",sepBy dProb xs ",",Ds ")"]


sepBy f xs comma = Dr (intersperse (Ds comma) (map f xs))
intersperse x [] = []
intersperse x [y] = [y]
intersperse x (y:ys) = y:x: intersperse x ys

dST (step,sol,disp,exceed) = Dr [Dd "(steps = ",Dd step
                                ,Ds ",solutions = ",Dd sol
                                ,Ds ",exceeded = ",Dd exceed,Dd ")"]


dRel :: Rel Tau -> DispElem Z
dRel (EqR(x,y)) = Dr [Ds "Equal ",dparen x,Ds " ",dparen y]
dRel (AndR xs) = Dr [Ds "and(",sepBy dRel xs ",",Ds ")"]

dSol :: Sol -> String -> DispElem Z
dSol = Dlf f
  where f d (prob,rel,(ls,un)) = displays d [Ds "\nProblem = ",dProb prob
                               ,Ds "\nTruths = ",dRel rel
                               ,Ds "\nUnifier = ",Dlf exhibitVT un ", "]


instance (Exhibit (DispInfo Z) name, Exhibit (DispInfo Z) var, Exhibit (DispInfo Z) term)
       => Exhibit (DispInfo Z) (NS name var term) where
  exhibit d (VarN x) = exhibit d x
  exhibit d (ConN name terms) = displays d [Ds "(",Dd name,Ds " ",Dl terms " ",Ds ")"]
  exhibit d (FunN name terms) = displays d [Ds "{",Dd name,Ds " ",Dl terms " ",Ds "}"]
  exhibit d (RelN x) = exhibit d x


instance Exhibit (DispInfo Z) (Prob Tau) where
  exhibit d (TermP x) = exhibit d x
  exhibit d eq@(EqP _) = displays d [dProb eq]
  exhibit d and@(AndP _) = displays d [dProb and]


instance Exhibit (DispInfo Z) a => Exhibit (DispInfo Z) (Rel a) where
  exhibit d (EqR(x,y)) = displays d [Ds "Equal (",Dd x,Ds ") (",Dd y,Ds ")"]
  exhibit d (AndR xs) = displays d [Ds "and(",Dl xs ",",Ds ")"]

instance Show NName where
  show (NTyCon a sx lev b) = a
  show NTyApp = "@"
  show (NStar n) = "*"++show n
  show NKarr = "~>"
  show (NTyVar nm k) = show nm
  show (NSkol n s k) = "!"++show n

instance Exhibit (DispInfo Z) NName where
  exhibit d (NTyCon a sx lev b) = exhibit d a
  exhibit d NTyApp = (d,"@")
  exhibit d (NStar n) = (d,"*"++show n)
  exhibit d NKarr = (d,"~>")
  exhibit d(NTyVar nm k) = exhibit d (TyVar nm k)
  exhibit d (NSkol n s k) = exhibit d (TcTv (Tv n (Skol s) k))

---------------------------------------------------------------------
-- helper functions for constructing terms

andR [x] = x
andR xs = AndR xs

andP [x] = x
andP xs = AndP xs

fun n ys = inject(FunN n ys)
con n ys = inject(ConN n ys)
eq [x,y] = inject(RelN (EqR (x,y)))
eqf x y = teq x y
andf x y = fun andName [x,y]

dispOf (x,y,d,z) = d

prop = MK propT
andKind = poly (karr prop (karr prop prop))
success = TyCon Ox (lv 1) "Success" (poly(MK propT))
andName = NTyCon "and" Ox (lv 1) andKind

varWildM (Tv _ _ k) =
  do { n <- nextInteger
     ; r <- newRef Nothing
     ; return(Tv n (Flexi r) k)}
     
termWildM t = 
  do { k <- kindOfM t 
     ; return(TcTv (wild (MK k))) }
     

equalP (TyApp (TyApp (TyCon sx _ "Equal" k) x) y) = True
equalP _ = False

equalParts (TyApp (TyApp (TyCon sx _ "Equal" k) x) y) = (x,y)


varWild (Tv _ _ k) = TcTv(wild k)
{-
termWild t = case kindOf t of
               Just k -> TcTv (wild (MK k))
              --  Nothing -> TcTv (wild star)
              -}

-- There is unique variable "WildCard" that is different from all
-- other type variables. It is unique, but different. Its actual
-- value doesn't matter, since it is never looked at, only its identity.
-- Sometimes we need versions with the same identity, but different
-- kinds. varWild, termWild, and termWildM compute one of these.

wild = unsafePerformIO (do { n <- nextInteger; r <- newRef Nothing; return(Tv n (Flexi r))})

---------------------------------------------------
-- Manipulating and combining Answers

-- nCons:: NTerm z n v t => (t,Un v t) -> NResult v t -> NResult v t
nCons x (Answers xs) = Answers(x : xs)
nCons x (Exceeded xs) = Exceeded(x: xs)

nAppend xs (Answers ys) = Answers(xs++ys)
nAppend xs (Exceeded ys) = Exceeded(xs++ys)

-------------------------------------------------------
-- Making fresh copies of terms. I.e. replacing every
-- var with a fresh var.

termFresh t = 
  do { k <- kindOfM t 
     ; newTau (MK k)
     }


varFresh (Tv u f (MK k)) = do {k1 <- freshN k; newTau (MK k1)}

freshX (vs,ps,term) =
  do { ns <- mapM varFresh vs
     ; let subT = zip vs ns
     ; return(subTau subT ps,subTau subT term)}

-- freshen :: (NMonad z n v t m) => t -> m t
freshen x =
  case project x of
   (VarN s) -> varFresh s
   (FunN n xs) -> do { ys <- mapM freshen xs; return(fun n ys)}
   (ConN n xs) -> do { ys <- mapM freshen xs; return(con n ys)}
   (RelN (EqR (x,y))) -> do { a <- freshen x; b <- freshen y; return(eq [a,b]) }


freshN :: TyCh m => Tau -> m Tau
freshN (TyVar n (MK k)) = do { k2 <- freshN k; return(TyVar n (MK k2))}
freshN (TyApp x y) = do { a <- freshN x; b <- freshN y; return(TyApp a b)}
freshN (Star n) = return(Star n)
freshN (Karr x y) = do { a <- freshN x; b <- freshN y; return(Karr a b)}
freshN (TyFun s p xs) = do { p2 <- freshPoly p; ys <- mapM freshN xs; return(TyFun s p2 ys)}
freshN (TcTv (Tv n (Flexi ref) (MK k))) = do { k2 <- freshN k; newTau (MK k2)}
freshN (TcTv (Tv n f (MK k))) = do { k2 <- freshN k; return(TcTv (Tv n f (MK k2)))}
freshN (TySyn s n xy ys t) = freshN t
freshN (TyEx xs) = do { t2 <- freshN t
                      ; ps2 <- mapM freshPred ps
                      ; return(TyEx (windup vs (ps2,t2)))}
 where (vs,(ps,t)) = unsafeUnwind xs
freshN (TyCon sx level n k) = do { k2 <- freshPoly k; return(TyCon sx level n k2)}

freshPoly :: TyCh m => PolyKind -> m PolyKind
freshPoly (K lvs s) = do { s2 <- freshSig s; return(K lvs s2)}

freshSig :: TyCh m => Sigma -> m Sigma
freshSig (Forall xs) = do { rho2 <- freshRho rho
                          ; ps2 <- mapM freshPred ps
                          ; return(Forall (windup vs (ps2,rho2)))}
  where (vs,(ps,rho)) = unsafeUnwind xs


freshRho :: TyCh m => Rho -> m Rho
freshRho (Rtau t) = do { t2 <- freshN t; return(Rtau t2)}
freshRho (Rarrow s r) = do { s2 <- freshSig s; r2 <- freshRho r; return(Rarrow s2 r2)}
freshRho (Rpair s r) = do { s2 <- freshSig s; r2 <- freshSig r; return(Rpair s2 r2)}
freshRho (Rsum s r) = do { s2 <- freshSig s; r2 <- freshSig r; return(Rsum s2 r2)}

freshPred (Rel t) = do { t2 <- freshN t; return(Rel t2)}
freshPred (Equality x y) = do { a <- freshN x; b <- freshN y; return(Equality a b)}
