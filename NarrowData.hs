-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Mon Nov 13 16:07:17 Pacific Standard Time 2006
-- Omega Interpreter: version 1.3

module NarrowData where

import System.IO.Unsafe(unsafePerformIO)
import RankN
import Bind(Name)
import Auxillary
import Monads

-------------------------------------------------------------------
-- When narrowing we need to partition terms into 4 classes
-- 1) variables, 2) constructors, 3) function calls, 4) Predicates
-- To do this we provide the type NS. Terms are composed of
-- Names (of constructors or constants), Variables, and Subterms.
-- We provide projection (Tau -> NS) functions and injection (NS -> Tau)
-- functions. This way we need only write the code once that decides
-- what class a term is in.

data NName
  = NTyCon String PolyKind
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

type Sol = [(Prob Tau,Rel Tau,Unifier)]
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
   Just(nm,k,xs) -> ConN (NTyCon nm k) xs
   Nothing -> ConN NTyApp [x,y]
project x@(Star n) = ConN (NStar n) []
project (Karr a b) = ConN NKarr [a,b]
project (TyFun s p xs) = FunN (NTyCon s p) xs
project (TcTv (Tv n (Skol s) k)) = ConN (NSkol n s k) []
project (TcTv s) = (VarN s)
project (TySyn s n xy ys t) = project t
project x@(TyEx _) = error ("Can't project anonymous existential types: "++show x)
project (TyCon level_ n k) = ConN (NTyCon n k) []

inject :: NS NName TcTv Tau -> Tau
inject (VarN s) = (TcTv s)
inject (FunN (NTyCon n k) xs) = TyFun n k xs
inject (ConN (NTyVar n k) []) = TyVar n k
inject (ConN NTyApp [x,y]) = TyApp x y
inject (ConN (NStar n) []) = Star n
inject (ConN NKarr [a,b]) = Karr a b
inject (ConN (NSkol n s k) []) = TcTv (Tv n (Skol s) k)
inject (ConN (NTyCon n k) xs) = f (TyCon (lv 1 {- TODO LEVEL -}) n k) xs
  where f x [] = x
        f x (y:ys) = f (TyApp x y) ys
inject (RelN (EqR(x,y))) = teq x y

---------------------------------------------------------------------
-- relations (Rel) and Problems (Prob) are type-like

instance TypeLike m a => TypeLike m (Prob a) where
  sub env (TermP x) = do { a <- sub env x; return (TermP a) }
  sub env (EqP(x,y)) = do { a <- sub env x; b <- sub env y; return (EqP(a,b)) }
  sub env (AndP xs) = do { as <- mapM (sub env) xs; return (AndP as) }

  zonk (TermP x) = do { a <- zonk x; return (TermP a) }
  zonk (EqP(x,y)) = do { a <- zonk x; b <- zonk y; return (EqP(a,b)) }
  zonk (AndP xs) = do { as <- mapM (zonk) xs; return (AndP as) }

  get_tvs (TermP x) = get_tvs x
  get_tvs (EqP(x,y)) = binaryLift unionP (get_tvs x) (get_tvs y)
  get_tvs (AndP xs) = get_tvs xs

  nf (TermP x) = do { a <- nf x; return (TermP a) }
  nf (EqP(x,y)) = do { a <- nf x; b <- nf y; return (EqP(a,b)) }
  nf (AndP xs) = do { as <- mapM (nf) xs; return (AndP as) }


instance TypeLike m a => TypeLike m (Rel a) where
  sub env (EqR(x,y)) = do { a <- sub env x; b <- sub env y; return (EqR(a,b)) }
  sub env (AndR xs) = do { as <- mapM (sub env) xs; return (AndR as) }

  zonk (EqR(x,y)) = do { a <- zonk x; b <- zonk y; return (EqR(a,b)) }
  zonk (AndR xs) = do { as <- mapM (zonk) xs; return (AndR as) }

  get_tvs (EqR(x,y)) = binaryLift unionP (get_tvs x) (get_tvs y)
  get_tvs (AndR xs) = get_tvs xs

  nf (EqR(x,y)) = do { a <- nf x; b <- nf y; return (EqR(a,b)) }
  nf (AndR xs) = do { as <- mapM (nf) xs; return (AndR as) }

instance Eq NName where
 (NTyCon a b) == (NTyCon c d) = a==c
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
dProb (AndP xs) = Dr [Ds "and(",Dr (map dProb xs),Ds ")"]


dST (step,sol,disp,exceed) = Dr [Dd "(steps = ",Dd step
                                ,Ds ",solutions = ",Dd sol
                                ,Ds ",excceeded = ",Dd exceed,Dd ")"]


dRel :: Rel Tau -> DispElem Z
dRel (EqR(x,y)) = Dr [Ds "Equal ",dparen x,Ds " ",dparen y]
dRel (AndR xs) = Dr [Ds "and(",Dr (map dRel xs ),Ds ")"]

dSol :: Sol -> String -> DispElem Z
dSol = Dlf f
  where f d (prob,rel,un) = displays d [Ds "\nProblem = ",dProb prob
                               ,Ds "\nTruths = ",dRel rel
                               ,Ds "\nUnifier = ",Dl un ", "]


instance Exhibit (DispInfo Z) a => Exhibit (DispInfo Z) (Prob a) where
  exhibit d (TermP x) = exhibit d x
  exhibit d (EqP(x,y)) = displays d [Ds "Equal (",Dd x,Ds ") (",Dd y,Ds ")"]
  exhibit d (AndP xs) = displays d [Ds "and(",Dl xs ",",Ds ")"]


instance Exhibit (DispInfo Z) a => Exhibit (DispInfo Z) (Rel a) where
  exhibit d (EqR(x,y)) = displays d [Ds "Equal (",Dd x,Ds ") (",Dd y,Ds ")"]
  exhibit d (AndR xs) = displays d [Ds "and(",Dl xs ",",Ds ")"]

instance Show NName where
  show (NTyCon a b) = a
  show NTyApp = "@"
  show (NStar n) = "*"++show n
  show NKarr = "~>"
  show (NTyVar nm k) = show nm
  show (NSkol n s k) = "!"++show n

instance Exhibit (DispInfo Z) NName where
  exhibit d (NTyCon a b) = exhibit d a
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
success = TyCon (lv 1) "Success" (poly(MK propT))
andName = NTyCon "and" andKind
varWild (Tv _ _ k) = TcTv(wild k)
termWild t = TcTv (wild (MK(kindOf t)))

equalP (TyApp (TyApp (TyCon _ "Equal" k) x) y) = True
equalP _ = False

equalParts (TyApp (TyApp (TyCon _ "Equal" k) x) y) = (x,y)

equalPartsM (TyApp (TyApp (TyCon _ "Equal" k) x) y) = return (x,y)
equalPartsM _ = fail "Not an Equality"

wild = unsafePerformIO (do { n <- nextInteger; r <- newRef Nothing; return(Tv n (Flexi r))})

---------------------------------------------------
-- Manipulating and copmbining Answers

-- nCons:: NTerm z n v t => (t,Un v t) -> NResult v t -> NResult v t
nCons x (Answers xs) = Answers(x : xs)
nCons x (Exceeded xs) = Exceeded(x: xs)

nAppend xs (Answers ys) = Answers(xs++ys)
nAppend xs (Exceeded ys) = Exceeded(xs++ys)

-------------------------------------------------------
-- Making fresh copies of terms. I.e. replacing every
-- var with a fresh var.

termFresh t = newTau (MK(kindOf t))

varFresh (Tv u f k) = newTau k

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

