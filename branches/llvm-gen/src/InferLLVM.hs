-- Copyright (c) Gabor Greif
-- email ggreif gmail com
-- Subject to conditions of distribution and use; see LICENSE.txt for details.

{-# OPTIONS_GHC -fglasgow-exts -fallow-undecidable-instances #-}
module InferLLVM() where

import Bind
import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import System.IO.Unsafe(unsafePerformIO)
import Monads
import Monad(when,foldM)

import RankN
import Syntax(Exp(..),Lit(..),Ev,Var)
import qualified Data.Map as Map
import Auxillary(plist,plistf,Loc(..),report,foldrM,foldlM,extend,extendL,backspace,prefix
                ,DispInfo(..),Display(..),newDI,dispL,disp2,disp3,disp4,tryDisplay
                ,DispElem(..),displays,ifM,anyM,allM,maybeM,eitherM,dv,dle,ns)


data LLType where
  LLInt :: LLType
  LLPtr :: LLType
  LLPair :: LLType -> LLType -> LLType
  LLTv :: TcTv -> LLType
 deriving (Show)


instance (HasIORef m,Fresh m) => Zonk m LLType where
 zonkG = zonkLL
 tvs = tvs_LL


zonkLL :: (HasIORef m,Fresh m) => LLType -> m LLType
zonkLL a@LLInt = return a
zonkLL a@LLPtr = return a
zonkLL (LLPair x y) = binaryLift pair (zonkLL x) (zonkLL y)
zonkLL (LLTv (Tv un flav k)) = do { k2 <- zonkKind k; return (LLTv (Tv un flav k2)) }

pair :: LLType -> LLType -> LLType
pair x y = LLPair x y

tvs_LL :: (HasIORef m,Fresh m) => LLType -> m([TcTv],[TcLv])
tvs_LL LLInt = return ([], [])
tvs_LL LLPtr = return ([], [])
tvs_LL (LLPair x y) = binaryLift unionP (tvs_LL x) (tvs_LL y)
--tvs_LL (LLTv v) = tvs v

instance TyCh m => TypeLike m LLType where
  sub = undefined

instance (TypeLike m LLType,TyCh m) => Typable m Lit LLType where
  check = checkLit
  infer = inferLit -- :: term -> m (ty,term)

checkLit e@(Int _) LLInt = return e
checkLit e LLPtr = return e -- generic representation
checkLit e t = fail (show e ++ " does not check as " ++ show t)

inferLit e@(Int _) = return (LLInt, e)


instance (TypeLike m LLType,TyCh m) => Typable m Exp LLType where
  -- tc = undefined -- :: term -> Expected ty -> m term
  check = checkLL -- :: term -> ty -> m term
  infer = undefined -- :: term -> m (ty,term)

checkLL :: TyCh m => Exp -> LLType -> m Exp
checkLL e@(Lit l) t = do { _ <- check l t; return e }
checkLL e@(Prod e1 e2) (LLPair t1 t2) = do
                                        c1 <- checkLL e1 t1
                                        c2 <- checkLL e2 t2
                                        return (Prod c1 c2)

type FiniteMap k a = Map.Map k a

data LLTcEnv
  = LLTcEnv { var_env :: FiniteMap Var Exp -- Term Vars
          --, type_env :: [(String,Tau,PolyKind)] -- Type Vars
          --, generics :: [(Var,Sigma)]    -- Lambda Bound Names
          --, level :: CodeLevel           -- code level, counts brackets
          , location :: Loc              -- position in file
          --, bindings :: MGU              -- equality bindings
          --, assumptions :: [Pred]        -- assumptions
          --, rules :: FiniteMap String [RWrule] -- Proposition simplifying rules
          --, refutations :: FiniteMap String Refutation
          , runtime_env :: Ev            -- current value bindings
          --, imports :: [(String,TcEnv)]  -- already imported Modules
          --, tyfuns :: [(String,DefTree TcTv Tau)]
          --, sourceFiles :: [String]
          --, syntaxExt :: [SynExt String]
          }

getLoc :: LLTC Loc
getLoc = Tc (\ env -> return (location env,[]))

instance TracksLoc (Mtc LLTcEnv Pred) Z where
  position = do { l <- getLoc; return l}
  failN loc n k s = Tc h
    where h env = FIO(return(Fail loc n k s))


instance TyCh (Mtc LLTcEnv Pred) where
   envTvs = undefined -- do { (vs,triples) <- getVarsFromEnv; return vs}
   handleK = undefined -- handleTC
   assume preds unifier m = undefined -- 
        --do { env <- tcEnv
        --   ; let env2 = env { bindings = composeMGU unifier (bindings env)
        --                    , assumptions = preds ++ (assumptions env) }
        --   ; inEnv env2 m
        --   }
   getBindings = undefined -- getBs
   getDisplay = undefined -- readRef dispRef
   solveSomeEqs p preds = undefined -- do { env <- tcEnv; (u,ps,_,_) <- solveConstraints p env preds; return(ps,u)}
   show_emit = undefined -- getMode "predicate_emission"
   getTruths = undefined -- getAssume
   setTruths = undefined -- setAssumptions
   currentLoc = undefined -- getLoc
   syntaxInfo = undefined -- getSyntax
   normTyFun = undefined -- normTyFunTau
   fromIO = undefined -- io2Mtc


type LLTC a = Mtc LLTcEnv Pred a

