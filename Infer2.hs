-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Thu Oct 12 08:42:26 Pacific Daylight Time 2006
-- Omega Interpreter: version 1.2.1

module Infer2 where

import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import System.IO.Unsafe(unsafePerformIO)

import Monad(when,foldM)
import Monads(Mtc(..),runTC,testTC,unTc,handleTC,TracksLoc(..)
             ,Exception(..)
             ,FIO(..),fio,failP,fio2Mtc,runFIO
             ,HasNext(..),outputString
             ,extractAccum,injectAccum
             ,readRef,newRef,writeRef,HasIORef()
             ,writeln
             )
import Bind
import Syntax
import RankN hiding (Level)
import List((\\),partition,sort,sortBy,nub,union,unionBy
           ,find,deleteFirstsBy,groupBy,intersect)
import Encoding2
import Auxillary(plist,plistf,Loc(..),report,foldrM,extend,extendL,backspace
                ,DispInfo(..),Display(..),newDI,dispL,disp2,disp3,disp4
                ,DispElem(..),displays,mergeDisp,ifM,anyM,allM,maybeM,dv)
import LangEval(vals,env0,Prefix(..),elaborate)
import ParserDef(pCommand,parseString,Command(..),getExp)
import Char(isAlpha)
import ParserDef(parse2, program)
import System.IO.Unsafe(unsafePerformIO)
-- import IOExts(unsafePerformIO)
import SCC(topSortR)
import NarrowMod
import Cooper(Formula(TrueF,FalseF),Fol,Term,toFormula,integer_qelim,Formula)

import qualified System.Console.Readline as Readline

import qualified Data.Map as Map
   (Map,empty,member,insertWith,union
   ,fromList,toList,lookup)



type FiniteMap k a = Map.Map k a
addListToFM map list = Map.union (Map.fromList list) map


pstr :: String -> TC ()
pstr = outputString


appendFM map key element = Map.insertWith add key [element] map
  where add old new = (old ++ new)

appendFM2 map [] = map
appendFM2 map ((key,element):xs) = Map.insertWith add  key element (appendFM2 map xs)
  where add old new = old ++ new

appendFMmany map []  = map
appendFMmany map ((k,e):xs) = appendFMmany (appendFM map k e) xs


---------------------------------------------------------------------------
-- Set up the TC monad

localRename = False

type TC a = Mtc Z TcEnv Pred a

inEnv :: TcEnv -> TC c -> TC c
inEnv env (Tc f) = Tc(\ x -> f env)
tcEnv :: TC TcEnv
tcEnv = (Tc (\ env -> return(env,[])))

instance TyCh (Mtc Z TcEnv Pred) where
   envTvs = do { (vs,triples) <- getVarsFromEnv; return vs}
   handleK = handleTC
   assume preds unifier m =
        do { env <- tcEnv
           ; let env2 = env { bindings = composeMGU unifier (bindings env)
                            , assumptions = preds ++ (assumptions env) }
           ; inEnv env2 m
           }
   getBindings = getBs
   getDisplay = (Tc ( \ env -> return(displayInfo env,[])))
   normFun = normTyFun
   normEq = normEqual

   solveSomeEqs = mguM

   show_emit = getMode "show_predicate_generation"
   getTruths = getAssume
   setTruths = setAssumptions
   peekPred = peek
   currentLoc = getLoc

getBs = do { env <- tcEnv; zonk(bindings env) }
getAssume = do { env <- tcEnv; zonk(assumptions env) }
collectPred :: TC a -> TC (a,[Pred])
collectPred x = do { (ans,ps) <- extractAccum x; ps2 <- zonk ps; return(ans,ps2) }


getMatchingRules s = do { env <- tcEnv; return(getRules s env)}

instance TracksLoc (Mtc Z TcEnv Pred) Z where
  position = do { l <- getLoc; return l}
  failN dis loc n k s = Tc h
    where h env = FIO(return(Fail dis loc n k s))

-------------------------------------------------------------------------
-- The type checking environment TcEnv and its auxillary data types

data Mod = Wob | Rig -- a Modifier is either Wobbly or Rigid


-- type ToEnv = [(String,Tau,PolyKind)] -- In RankN.hs
data Frag = Frag [(Var,(Sigma,Mod,Level,Exp))] [TcTv] ToEnv
                 [Pred] Unifier [(String,(RWrule))]

interesting (Frag env skols _ eqn theta rules) = not(null eqn)

nullFrag = Frag [] [] [] [] [] []

type Level = Int
type Refutation = Tau -> TC ()

-- The type of the internal environment of the Type Checking Monad
data TcEnv
  = TcEnv { var_env :: FiniteMap Var (Sigma,Mod,Level,Exp) -- Term Vars
          , type_env :: [(String,Tau,PolyKind)] -- Type Vars
          , generics :: [(Var,Sigma)]    -- Lambda Bound Names
          , level :: Int                 -- code level, counts brackets
          , location :: Loc              -- position in file
          , bindings :: MGU              -- equality bindings
          , assumptions :: [Pred]        -- assumptions
          , rules :: FiniteMap String [RWrule] -- Proposition simplifying rules
          , refutations :: FiniteMap String Refutation
          , runtime_env :: Ev            -- current value bindings
          , imports :: [(String,TcEnv)]  -- already imported Modules
          , displayInfo :: (DispInfo Z)  -- display info
          , tyfuns :: [(String,[Tau]-> TC Tau,DefTree TcTv Tau)]
          }

modes_and_doc =
  [("verbose",False,"Turns on tracing in the predicate solving engine.")
  ,("delay_narrowing",True,"When narrowing an equality such as (v = {\\tt \\{plus a b\\}}), binds the variable 'v' to {\\tt \\{plus a b\\}}, rather than narrowing the variable 'a' to constructors. The binding is then emitted as predicate to be solved later. This has the effect of delaying narrowing until more is known about 'v', 'a', or 'b'.")
  ,("show_predicate_generation",False,"Reports the fact that a prediciate has been emitted. Predicates are collected at generalization sites, and are either solved, or abstracted into constrained types.")
  ,("steps",False,"Shows the steps taken when narrowing. Useful for debugging when narraowing does not return the result desired.")
  ]

mode0 = map (\ (name,value,doc) -> (name,value)) modes_and_doc
tcEnvEmpty = TcEnv Map.empty toEnvX [] 0 Z [] [] Map.empty Map.empty env0 [] disp0 []

modes ::  IORef [(String,Bool)]
modes = unsafePerformIO(newIORef mode0)



----------------------------------------------------------
-- A class of data structures that are binding instances

class TypableBinder term where
  checkBndr :: Bool -> Mod -> Frag -> Sigma -> term -> TC(Frag,term)
  inferBndr :: Bool -> Frag -> term -> TC(Sigma,Frag,term)

----------------------------------------------------------------
-- simple operations on Frag and TcEnv
-- One can perform substitution and zonking on Frags

composeM (env@(_,s1,_,_)) s2 =
 do { let f (v,t) = do { t2 <- sub env t; return(v,t2) }
    ; prefix <- mapM f s2
    ; return(prefix ++ s1)}

instance TypeLike (Mtc Z TcEnv Pred) Frag where
  sub env (Frag xs ys zs eqs theta rs) =
     do { xs' <- mapM f xs;
        ; eqs2 <- sub env eqs
        ; zs' <- mapM g zs
        ; rs2 <- mapM (sub env) rs
        ; theta2 <- composeM env theta
        ; return(Frag xs' ys zs' eqs2 theta2 rs2)}
    where f (v,(s,mod,lev,exp)) = do { s2 <- sub env s; return(v,(s2,mod,lev,exp))}
          g (str,tau,kind) =
            do { t2 <- sub env tau; k2 <- sub env kind; return(str,t2,k2)}
  zonk (Frag xs ys zs eqs theta rs) =
    do { xs2 <- mapM f1 xs
       ; eqs2 <- mapM zonk eqs
       ; rs2 <- mapM zonk rs
       ; theta2 <- zonk theta
       ; return(Frag xs2 ys zs eqs2 theta2 rs2)}
   where f1 (x,(y,mod,z,w)) = do { y' <- zonk y; return(x,(y',mod,z,w))}
  get_tvs f = error "No way to get the type vars from a Frag"
  nf x = error "Can't put frags in normal form"

infixr +++    --- NOTE (+++) is NOT COMMUTATIVE, see composeU
(Frag xs ys zs eqs u1 rs1) +++ (Frag as bs cs eqs2 u2 rs2) =
  case (mergeMgu u1 u2) of
    Left u3 -> return (Frag (xs++as) (ys++bs) (zs++cs) (eqs ++ eqs2) u3 (rs1++rs2))
    Right (mess,t1,t2) -> failD 2 [Ds "Inconsistent types checking patterns: "
                               ,Dd t1,Ds " != ", Dd t2]

getTyFuns :: TC [(String,[Tau]-> TC Tau,DefTree TcTv Tau)]
getTyFuns = Tc (\ env -> return (tyfuns env,[]))

-- getBindings defined in RankN
-- getBindings = Tc (\ env -> return (bindings env,[]))
getAssumptions = Tc (\ env -> return (assumptions env,[]))

addPred :: [Pred] -> Frag -> TC Frag
addPred truths (Frag xs ys zs eqs theta rs) = return(Frag xs ys zs (truths++eqs) theta rs)

addSkol :: [TcTv] -> Frag -> Frag
addSkol vs (Frag xs ys zs eqs theta rs) = Frag xs (vs++ys) zs eqs theta rs

getTCEnv :: TC (FiniteMap Var (Sigma,Mod,Level,Exp))
getTCEnv = Tc (\ env -> return (var_env env,[]))

getGenerics :: TC [(Var,Sigma)]
getGenerics = Tc (\ env -> return (generics env,[]))

getLevel :: TC Int
getLevel = Tc (\ env -> return (level env,[]))

getLoc :: TC Loc
getLoc = Tc (\ env -> return (location env,[]))

getTypeEnv :: TC [(String,Tau,PolyKind)]
getTypeEnv = Tc (\ env -> return (type_env env,[]))

getkind :: Monad a => [Char] -> TcEnv -> a (PolyKind,Tau,[Char])
getkind x env = f (type_env env) (tyfuns env)
   where f [] ts = fail ("Unknown type: "++x)
         f ((y,t,k):xs) table | x==y =
            let p (nm,f,tree) = nm==x
            in case (find p table) of
                  Just (name,fun,tree) -> return(k,t,show tree)
                  Nothing -> return(k,t,"")
         f (x:xs) ts = f xs ts


showAllVals n env = mapM f (take n (Map.toList(var_env env)))
  where f (nm,(sigma,mod,level,exp)) = outputString (show nm ++ " : " ++alpha [] sigma)

showSomeVals p env = mapM f (filter p (Map.toList(var_env env)))
  where f (nm,(sigma,mod,level,exp)) = outputString (show nm ++ " : " ++alpha [] sigma)

showVals d1 vs = do { env <- getTCEnv
                    ; warnD d1 [Dlf f (filter p (Map.toList env)) "\n  "]}
  where p (Global s,_) = any (==s) vs
        f d (nm,(sigma,mod,level,exp)) = displays d [Ds (show nm++" :: "),Dd sigma]

showBindings d = do { bs <- getBindings; warnD d [Ds "bindings = ",Dl bs ", "]}
showAssumptions d = do { bs <- getAssumptions; warnD d [Ds "assumptions = ",Dl bs ", "]}

valueNames env = foldr add [] (Map.toList (var_env env))
  where add (Global nm,(sigma,mod,level,exp)) xs = nm:xs
        add _ xs = xs

typeNames env = map f (type_env env)  where f (name,tau,polykind) = name

completionEntry env = entry
  where tnames = typeNames env
        vnames = valueNames env
        all = nub(vnames ++ tnames)
        prefix [] s = True
        prefix (x:xs) (y:ys) | x==y = prefix xs ys
        prefix xs ys = False
        entry s = (filter (prefix s) all)

setMode :: (Monad m,HasIORef m) => String -> Bool -> m()
setMode name b =
  do { ms <- readRef modes
     ; let update [] = []
           update ((s,_):xs) | prefix name s = (s,b):xs
           update (x:xs) = x:(update xs)
     ; writeRef modes (update ms)
     }

getM :: (Monad m,HasIORef m) => String -> Bool -> m Bool
getM name defaultB =
  do { ms <- readRef modes
     ; let find [] = defaultB
           find ((s,b):xs) | prefix name s = b
           find(x:xs) = (find xs)
     ; return(find ms)
     }

mknoisy env = setMode "verbose" True >> return env
mksilent env = setMode "verbose" False >> return env
getMode :: String -> TC Bool
getMode s = getM s False

setDisplay :: DispInfo Z -> Mtc Z TcEnv a b -> Mtc Z TcEnv a b
setDisplay d (Tc m) = Tc(\env -> m (env {displayInfo = d}));

setAssumptions :: [Pred] -> Mtc Z TcEnv a b -> Mtc Z TcEnv a b
setAssumptions d (Tc m) = Tc(\env -> m (env {assumptions = d}));

--------------------------------------------------
-- Manipulating the environment part of the monad

letExtend :: Frag -> TC a -> TC a
letExtend (Frag pairs rigid tenv eqs theta rs) (Tc m) = Tc (\env -> m (extend env))
  where extend env = env { var_env = addListToFM (var_env env) pairs
                         , type_env = tenv ++ (type_env env)
                         , bindings = composeMGU theta (bindings env)
                         , assumptions = eqs ++ (assumptions env)
                         , rules = appendFMmany (rules env) rs}

lambdaExtend :: Frag -> TC a -> TC a
lambdaExtend (Frag pairs rigid tenv eqs theta rs) (Tc m) = Tc (\env -> m (extend env))
  where g (x,(rho,mod,lev,exp)) = (x,rho)
        extend env = env { var_env = addListToFM (var_env env) pairs
                         , generics = (generics env) ++ map g pairs
                         , bindings = composeMGU theta (bindings env)
                         , assumptions = eqs ++ (assumptions env)
                         , rules = appendFMmany (rules env) rs
                         }

-- FIX THETA
-- Run a computation under an extended environment that extends
-- only the facts in the environment
factExtend :: [Pred] -> MGU -> TC a -> TC a
factExtend preds unifier (Tc m) = Tc (\env -> m (extend env))
  where extend env = env { bindings = composeMGU unifier (bindings env)
                         , assumptions = preds ++ (assumptions env) }

underTypeEnv :: ToEnv -> TC a -> TC a
underTypeEnv new (Tc m) = Tc (\env -> m (extend env))
  where extend env = env { type_env = new ++ (type_env env) }

composeMGU :: MGU -> MGU -> MGU
composeMGU s1 s2 = ([(u,subTau s1 t) | (u,t) <- s2] ++ s1)

addFrag (Frag pairs rigid tenv eqs theta rs) env = extend env
  where extend env = env { var_env = addListToFM (var_env env) pairs
                         , type_env = tenv ++ (type_env env)
                         , bindings = composeMGU theta (bindings env)
                         , rules = appendFMmany (rules env) rs}
        (Left unifier) = mgu (map f eqs)   --- We used to use unifier, But no more.
        f (Equality x y) = (x,y)           -- FIX THETA

addLetFrag (Frag pairs rigid tenv eqs theta rs) env =
    env { var_env = addListToFM (var_env env) pairs
        , bindings = composeMGU theta (bindings env)
        , rules = appendFMmany (rules env) rs}
 where (Left unifier) = mgu (map f eqs)  --- We used to use unifier, But no more.
       f (Equality x y) = (x,y)          -- FIX THETA

levelInc :: TC a -> TC a
levelInc (Tc m) = Tc (\env -> m (env {level = (level env) + 1}))

levelDec :: TC a -> TC a
levelDec (Tc m) = Tc (\env -> m (env {level = (level env) - 1}))

newLoc :: Loc -> TC a -> TC a
newLoc loc (Tc m) = Tc (\env -> m (env {location = loc}))

lookupVar :: Var -> TC (Sigma,Mod,Level,Exp)    -- May fail
lookupVar n = do { env <- getTCEnv
                 ; case Map.lookup n env of
                     Just(ty@(sigma,mod,n,exp)) ->
                        case mod of
                          Wob -> return ty
                          Rig -> do { theta <- getBindings
                                    ; sig2 <- sub ([],theta,[],[]) sigma
                                    ; return(sig2,mod,n,exp)}
                     Nothing -> failD 2 [Ds "Not in scope: ", Dd n]}

getVar :: Var -> TcEnv -> Maybe(Sigma,Mod,Level,Exp)
getVar nm env = Map.lookup nm (var_env env)

getRules :: String -> TcEnv -> [(RWrule)]
getRules nm env =
  case Map.lookup nm (rules env) of
    Nothing -> []
    Just ts -> ts



-----------------------------------------------------------------
-- Types in syntax are stored as PT, we need to translate them
-- into Sigma types, and check that their well formed with Kind *
-- PT types stored in Data Decs are handled differently because they
-- may have kinds other than *, and they are not always generalized.
-- We return a Sigma type, and a Fresh Rho type, and a Display mapping
-- mapping the Vars in the fresh Rho to the Strings in the PT

checkPT :: PT -> TC(Sigma,([(Z,String)],Rho,[Pred],[TcTv]))
checkPT pt =
  do { tenv <- getTypeEnv
     ; (free,pt2) <- splitPT tenv pt  -- Make sure its an explcit Forallx form
     ; freeEnv <- mapM genFresh free  -- Make temp Types for translating free typevars
     ; (s@(Forall xs),snMap) <- toSigma (freeEnv ++ tenv) pt2 -- translate
     ; check s (Star 0)                                       -- check the translation has kind *0
     ; let (names,(eqns,rho)) = unsafeUnwind xs               -- unwind to make a fresh Rho instance
     ; (nameMap,stringMap,skol) <- rigid snMap names []            -- build the mappings
     ; rho2 <- sub (nameMap,[],[],[]) rho            -- make fresh Rho      -- TODO LEVEL
     ; eqn2 <- sub (nameMap,[],[],[]) eqns           -- and fresh equations -- TODO LEVEL
     ; return (s,(stringMap,rho2,eqn2,skol))}
 where  genFresh nm =
          do { kind <- newKind star1; var <- newFlexiTyVar kind
             ; return(nm,TcTv var,poly kind)}
       -- unique (Tv n f k) = ZTv n f k
        rigid ((s,nm):xs) ((nm2,k,q):ys) subst =
            do { k2 <- sub (subst,[],[],[]) k -- in explicit foralls, earlier may bind -- TODO LEVEL
               ; v <- newRigidTyVar q Z s k2  -- later, so we need to apply subst to k
               ; (subst2,ms,skols) <- rigid xs ys ((nm,TcTv v):subst)
               ; return(subst2,(ZTv v,"_"++s):ms,v:skols)}
        rigid _ _ subst = return(subst,[],[])

-- prototypes can be one of two forms
-- implicit, like: f :: (a -> b) -> [a] -> [b]
-- explicit, like: f :: forall a b . (a -> b) -> [a] -> [b]
-- check for free vars in explicit case, and always return an explicit case

splitPT :: ToEnv -> PT -> TC([String],PT)
splitPT tenv pt =
   case pt of
    Forallx All xs eqs rho ->
       case free of
         [] -> return(free,Forallx All xs eqs rho)
         vs -> failD 1 [Ds "The explicit, universally quantified prototype\n  "
                       ,Dd pt
                       ,Ds "\nhas free variables: "
                       ,Dl vs "," ]
    rho -> return(free,Forallx All (map g free) [] rho)
 where free = getFree (map name tenv) pt
       name (nm,tau,kind) = nm
       g nm = (nm,AnyTyp 1,All)

-- In a type synonym like:
-- type ListInt = [ Int ]
-- the type must be well kinded in the current environment

inferPT :: ToEnv -> PT -> TC(Tau,Kind,PolyKind)
inferPT argEnv pt =
  do { tenv <- getTypeEnv
     ; s <- toTau (argEnv ++ tenv) pt
     ; (k::Tau,ty) <- infer s
     ; return(ty,MK k,poly(MK k))
     }

inferPolyPT :: ToEnv -> PT -> TC(Sigma,Kind,PolyKind,[(String,Name)])
inferPolyPT argEnv pt =
  do { tenv <- getTypeEnv
     ; (s,names) <- toSigma (argEnv ++ tenv) pt
     ; (k::Tau,ty) <- infer s
     ; return(ty,MK k,poly(MK k),names)
     }

--------------------------------------------------------------------
-- Literals are Typable

instance Typable (Mtc Z TcEnv Pred) Lit Rho where
  tc x@(Int n) expect = zap x (Rtau intT) expect
  tc x@(Char c) expect = zap x (Rtau charT) expect
  tc x@(Unit) expect = zap x (Rtau unitT) expect
  tc x@(ChrSeq s) expect = zap x (Rtau chrSeqT) expect
  tc x@(Symbol n) expect = zap x (Rtau symbolT) expect
  tc x@(Float n) expect = zap x (Rtau floatT) expect
  tc x@(Tag s) expect = zap x (Rtau (tlabel(ttag ('`':s)))) expect

--------------------------------------------------------------------
-- Functions to report reasonably readable  errors

notfun e fun_ty dis s =
   failDd "notfun" 2 dis [Ds "\nIn the expression: "
                ,Dd e
                ,Ds "\nthe function has a non-functional type: "
                ,Dd fun_ty]

badarg e arg_ty dis s =
 do { z <- zonk arg_ty
    ; failDd "badarg" 2 dis
       [Ds "\nIn the expression: "
       ,Dd e
       ,Ds "\nthe argument did not have type: "
       ,Dn arg_ty
       ,Ds s]}

resulterr e res_ty expect dispInfo s =
  do { ex <- case expect of {Check t -> return t; Infer ref -> readRef ref }
     ; rt <- zonk res_ty
     ; ex2 <- zonk ex
     ; info <- getDisplay
     ; info1 <- return(mergeDisp dispInfo info)
     ; refinement <- getBindings
     ; failDd "resulterr" 2 info1
         [Ds "\nIn the expression: "
         ,Dn e
         ,Ds "the result type: "
         ,Dn rt
         ,Ds "was not what was expected: "
         ,Dn ex
         ,Ds "refinement: ",Dl refinement ", "
         ,Ds ("\n"++s)
         ]}

morePoly::(Show a,Exhibit (DispInfo Z) a,Exhibit (DispInfo Z) b
          ,Exhibit (DispInfo Z) c,Subsumption m b(Expected c)
          ,TypeLike m b,TypeLike m c)
          => a -> b -> Expected c -> m ()
morePoly exp sigma expect =
   handleM 2 (morepoly (show exp) sigma expect) (resulterr exp sigma expect)


--------------------------------------------------------------------
-- This instance is useful for a first class pattern decl like:
-- pattern LHS = RHS
-- pattern If x y z = Case x [(True,y),(False z)]
-- where we need to check that the pattern on the RHS is well formed
-- when using the variables defined on the LHS.

instance Typable (Mtc Z TcEnv Pred) Pat Rho where
  tc (Plit l) expect = do { l2 <- tc l expect; return(Plit l2) }
  tc (Pvar v) expect =
     do { (sigma,mod,n,Var u) <- lookupVar v
        ; morePoly (Pvar v) sigma expect
        ; return(Pvar u)}
  tc (z@(Pexists p)) _ =
     failD 1 [Ds "No exist patterns in pattern decls: ",Dd z]
  tc pat@(Psum inj x) (Check (Rsum t1 t2)) = -- t1 or t2 or both are non-trivial Sigmas
     do { (sig::Sigma,e) <- infer x
        ; case inj of { L -> morepoly (show pat) t1 sig
                      ; R -> morepoly (show pat) t2 sig }
        ; return (Psum inj e) }
  tc (Psum inj x) expect =
     do { (a,b) <- expecting "Sum" tsum expect
        ; e <- check x (case inj of { L -> a; R -> b })
        ; return(Psum inj e) }

  tc p@(Pprod x y) (Check (Rpair t1 t2)) = -- t1 or t2 or both are non-trivial Sigmas
     do { (s1::Sigma,e1) <- infer x
        ; (s2::Sigma,e2) <- infer y
        ; morepoly (show p) t1 s1
        ; morepoly (show p) t2 s2
        ; return (Pprod e1 e2) }
  tc (Pprod x y) expect =
     do { (a,b) <- expecting "Pair" tpair expect
        ; e1 <- check x a
        ; e2 <- check y b
        ; return (Pprod e1 e2) }

  tc p@(Pcon c ps) expect =
     do { (sigma,mod,n,exp) <- lookupVar c
        ; loc <- getLoc
        ; (rigid,assump,rho) <- instanPatConstr Ex loc (show p) sigma
        ; ps2 <- checkArgs ps rho expect
        ; return (Pcon c ps2)
        }
  tc p expect = failD 2 [Ds "Bad pattern on RHS of pattern decl: ",Dd p]


---------------------------------------------------------------------------
-- Instances of the Binding syntactic categories: Var, Pat, [Pat], and [Dec]

alphaN :: Fresh m => Bool -> Var -> m Var
alphaN True (Global s)  = do { nm <- fresh; return(Alpha s nm)}
alphaN True (Alpha s _) = do { nm <- fresh; return(Alpha s nm)}
alphaN False name = return name

instance TypableBinder Var where
  checkBndr rename mod k t var =
     do { level <- getLevel
        ; v <- alphaN rename var
        ; return(addTermVar (var,(t,Rig,level,Var v)) k,v) }
  inferBndr rename k var =
     do { sigma <- newSigma star;
        ; level <- getLevel
        ; v <- alphaN rename var
        ; return(sigma,addTermVar (var,(sigma,Wob,level,Var v)) k,v) }

-- Suppose we have the following assumptions
--  _g=Univ, _h=e, _i=f, _j=f
-- We need to generate the extra assumption:   _i=_j

sameRhs:: [(Tau,Tau)] -> [(Tau,Tau)]
sameRhs [] = []
sameRhs (x@(xlhs,xrhs):xs) = (pairUp (x:matches)) ++ sameRhs xs
  where matches = filter (\ (lhs,rhs) -> rhs==xrhs) xs
        pairUp [] = []
        pairUp [x] = []
        pairUp ((x,y):(xs@((w,z):_))) = (x,w): pairUp xs

zonkLikePreds eqs =
      (case mostGenUnify  varTauPairs of  -- hopefully_unifier of
        Just us -> return(ps++map f us)
        Nothing -> warn [Ds "In zonkLikePreds unify fails on ",Dl (map g eqs2) "\n  "
                        ,Ds (shtt (fst(head(map g eqs2))))
                        ,Ds (shtt (snd(head(map g eqs2))))] >>
                   error "STOP")

 where (ps,eqs2) = splitU eqs
       f (v,tau) = Equality (TcTv v) tau
       g (v,tau) = (TcTv v,tau)
       varTauPairs = (map g eqs2)
       hopefully_unifier = varTauPairs ++ (sameRhs varTauPairs)

------------------------------------------------------------
--
type Kappa = Frag

addTermVar p (Frag terms pvs types eqs theta rules) =
             (Frag (p:terms) pvs types eqs theta rules)

addUnifier u (Frag terms pvs types eqs theta rules) =
   case (mergeMgu u theta) of
     Left u2 -> return(Frag terms pvs types eqs u2 rules)
     Right(s,t1,t2) -> failD 2 [Ds "Inconsistent types checking patterns: "
                               ,Dd t1,Ds " != ", Dd t2]


addEqs ps (Frag terms pvs types eqs theta rules)  =
          (Frag terms pvs types (subPred theta (ps ++ eqs)) theta rules)
addPVS vs (Frag terms pvs types eqs theta rules) =
          (Frag terms (vs++pvs) types eqs theta rules)
applyTheta Rig (Frag terms pvs types eqs theta rules) term = sub ([],theta,[],[]) term
applyTheta Wob frag term = return term
addRules rs (Frag terms pvs types eqs theta rules) =
            (Frag terms pvs types eqs theta (rs ++ rules))
getToEnv (Frag terms pvs types eqs theta rules) = types
getTermVars (Frag terms pvs types eqs theta rules) = map fst terms
getTheta (Frag terms pvs types eqs theta rules) = theta
getEqs (Frag terms pvs types eqs theta rules) = eqs


checkPats rename k [] = return(k,[])
checkPats rename k ((p,sig,mod):xs) =
  do { (k2,p2) <- checkPat rename mod k sig p
     ; (k3,ps2) <- checkPats rename k2 xs
     ; return(k3,p2:ps2)}

addVar (Forall(Nil([],Rtau (TcTv v)))) ty k = addUnifier [(v,ty)] k
addVar sig ty k = return k
nonRigidExists z =
  [Ds "Exists patterns cannot have their type inferred:\n  "
  ,Dd z,Ds " Use a prototype signature."]

badRefine pat t s x y =
  failD 2 [Ds "\nWhile infering the type of the pattern: ",Dd pat
          ,Ds "\nwe expected it to have type: ",Dd t
          ,Ds "\nbut, the current refinement fails because ",Dd x,Ds " != ",Dd y
          ,Ds ".\nSometimes reordering the patterns can fix this."]

badRefine2 pat theta t d s =
  failDd "bad refinement" 2 d
   [Ds "The current refinement: ",Dd theta,Ds "\nwont't type the pattern: "
   ,Dd pat,Ds " with type: ",Dd t
   ,Ds ".\nSometimes reordering the patterns can fix this.",Ds ("\n"++s)]

constrRange c [] rho pairs = do { tau <- okRange c rho; return(reverse pairs,tau)}
constrRange c (p:ps) t pairs =
   do { (dom,rng) <- unifyFun t
      ; constrRange c ps rng ((p,dom):pairs)}

okRange c (Rtau t) = return t
okRange c rho = failD 2 [Ds "\nNon tau type: ",Dd rho
                        ,Ds " as range of constructor: ",Dd c]

extendToEnv :: Frag -> TC TcEnv
extendToEnv frag =
  do { env <- tcEnv
     ; return(env{type_env = (getToEnv frag) ++ (type_env env)})}

-------------------------

checkPat :: Bool -> Mod -> Kappa -> Sigma -> Pat -> TC(Kappa,Pat)
checkPat rename mod k t pat =
  case (pat,mod) of
    (Plit x,_) -> handleM 2
       (do { expect <- applyTheta mod k t
           ; p <- check x expect
           ; return(k,Plit p)}) (badRefine2 pat (getTheta k) t)
    (Pvar var,_) ->
       do { level <- getLevel
          ; v <- alphaN rename var
          ; return(addTermVar (var,(t,mod,level,Var v)) k,Pvar v)}
    (Pcon c ps,Wob) ->
       do { (sigma@(Forall l),mod,n,exp) <- lookupVar c
          ; (vs,assump,rho) <- instanL l
          ; (pairs,range) <- constrRange c ps rho []
          ; morepoly "wobbly constr pattern" t (Rtau range)
          ; (bc,_) <- get_tvs range
          ; let hash xs ys = if null(intersect xs ys) then Rig else Wob
                -- if type vars are all existential (don't appear in range)
                -- then Mod is Rigid else its Wobbly
                addMod (pat,ty) =
                   do { (vs,_) <- get_tvs ty; return(pat,ty,hash vs bc)}
          ; triples <- mapM addMod pairs
          ; (k2,ps2) <- checkPats rename k triples
          ; let k3 = addEqs assump k2
          ; return(k3,Pcon c ps2)   }
    (Pcon c ps,Rig) ->
       do { (sigma@(Forall l),mod,n,exp) <- lookupVar c
          ; expect <- applyTheta Rig k t
          ; (vsC,assump,rhoC) <- rigidInstance (show pat) sigma
          ; (vsExpect,oblig,rhoExpect) <- rigidInstance (show pat) expect
          -- rhoC::    t1 -> t2 -> Ts s1 s2
          -- rhoExpect::           Tu u1 u2
          -- check that Tu==Ts, mguStar[(u1,s1),(u2,s2)]
          ; (pairs,tauC) <- constrRange c ps rhoC []
          ; tauExpect <- okRange c rhoExpect

          -- down (Tu u1 u2) (Ts s1 s2) ==> [(u1,s1),(u2,s2)] when Tu==Ts
          ; let down (u@(TyCon _ tu _)) (s@(TyCon _ ts _)) | tu==ts = return []
                down (u@(TyCon _ tu _)) (s@(TyCon _ ts _)) =
                  failD 2 [Ds ("\nWhile checking rigid pattern, expected constructor: "++tu++" doesn't match actual: "++ts)]
                down (TyApp tu u) (TyApp ts s) =
                  do { ps <- down tu ts; return((u,s):ps) }
                down x y = failD 2 [Ds "\nWhile checking rigid pattern: ",Dd pat
                                   ,Ds "\nexpected type: ",Dd expect
                                   ,Ds "\ndoesn't match actual type: ",Dd rhoC
                                   ,Ds "\nunder refinement: ",Dl (getTheta k) ", "]
                addRigid (pat,sigma) = (pat,sigma,Rig)
          ; thingsToUnify <- down tauExpect tauC
          ; eitherInfo <- mguStar vsC thingsToUnify
          ; case eitherInfo of
             Right(s,x,y) -> badRefine pat t s x y
             Left(psi,truths) ->
               do { k2 <- addUnifier psi (addPVS vsC k)
                  -- ; warn [Ds ("\n"++show pat++" psi = "),Dl psi ", "]
                  ; let k3 = addEqs (truths ++ subPred psi assump) k2
                  ; (k4,ps2) <- checkPats rename k3 (map addRigid pairs)
                  ; return(k4,Pcon c ps2)}
          }
    (Pprod x y,mod) ->
       do { pair <- applyTheta mod k t
          ; ((t1,t2),truths) <- collectPred (sigmaPair pair)
          ; (k2,x2) <- checkPat rename mod k t1 x
          ; (k3,y2) <- checkPat rename mod k2 t2 y
          ; return(addEqs truths k3,Pprod x2 y2)}
    (Psum inj p,mod) ->
       do { sum <- applyTheta mod k t
          ; ((t1,t2),truths) <- collectPred (sigmaSum sum)
          ; (k1,p1) <- checkPat rename mod k (case inj of {L -> t1; R -> t2}) p
          ; return(addEqs truths k1,Psum inj p1)}
    (z@(Pexists p),_) ->
       case t of
        Forall (Nil([],Rtau(TyEx zs))) ->
          do { loc <- getLoc
             ; (rigid,assump,tau) <- rigidInstanceL (show p) zs
             ; (k2,p2) <- checkPat rename Rig k (Forall(Nil([],Rtau tau))) p
             ; let k3 = addPVS rigid (addEqs assump k2)
             ; return(k3,Pexists p2) }
        _ -> failD 1 (nonRigidExists z)
    (Paspat var p,_) ->
       do { (k1,p1) <- checkPat rename mod k t p
          ; level <- getLevel
          ; v <- alphaN rename var
          ; return(addTermVar (var,(t,Rig,level,Var v)) k1,Paspat v p1)}
    (Pwild,_) -> return(k,Pwild)
    (Pann p ty,_) ->
       do { scopedEnv <- extendToEnv k
          ; (sigma,_) <- inEnv scopedEnv (checkPT ty)
          ; eitherInfo <- morepolySS [] t sigma
          ; case eitherInfo of
             Right(s,x,y) -> failD 2 [Ds "Annotation not polymorphic enough.\n"
                                     ,Ds s,Dd x,Dd y]
             Left(psi,truths) ->
               do { (k2,p') <- checkPat rename Rig k sigma p
                  ; k3 <- addUnifier psi k2
                  ; let k4 = addEqs truths k3
                  ; return(k4,Pann p' ty)}}

inferPat :: Bool -> Kappa -> Pat -> TC(Sigma,Kappa,Pat)
inferPat rename k pat =
  do { sigma <- newSigma star
     ; (k2,p2) <- checkPat rename Wob k sigma pat
     ; sigma2 <- zonk sigma
     ; return (sigma2,k2,p2)}

----------------------------------------------------------------------

instance TypableBinder Pat where
  checkBndr = checkPat
  inferBndr = inferPat


-----------------------------------------------------------------------

inferBndrs :: Bool -> Frag -> [Pat] -> TC([Sigma],Frag,[Pat])
inferBndrs rename k [] = return([],k,[])
inferBndrs rename k (p:ps) =
  do { (sig,k2,p2) <- inferBndr rename k p
     ; (sigs,k3,ps2) <- inferBndrs rename k2 ps
     ; return(sig:sigs,k3,p2:ps2)}


-- checkBndrs rename mod frag [p1,p2,p3] (t1 -> t2 -> t3 -> result)
-- checkThat:  theta <- check[p1:t1, p2:t2, p3:t3], and return theta(result)

checkBndrs :: Bool -> Mod -> Frag -> [Pat] -> Rho -> TC(Frag,[Pat],Rho)
checkBndrs rename mod k ps result_ty = checkBs disp0 rename mod k ps result_ty

sigmaRho (Forall l) = rho
  where (vs,(ps,rho)) = unsafeUnwind l

checkBs d rename mod f0 [] result =
  do { ty <- applyTheta Wob f0 result; return(f0,[],ty) }
checkBs d rename mod f0 (p:ps) rho =
  do { (dom,rng) <- unifyFun rho
     ; (f1,p1) <- checkPat rename mod f0 dom p
     ; rng2 <- applyTheta Wob f1 rng
     ; (f2,ps2,rng3) <- checkBs d rename mod f1 ps rng2
     ; return(f2,p1:ps2,rng3)
     }


type Binding = (Var,(Sigma,Mod,Level,Exp))

mErr (n::Int) (vs::[Binding]) eqs p dom d1 mess =
  do {truths <- getBindings
     ; failDd "mguErr" 2 d1
        [Ds "\nWhile checking that the pattern "
        ,Dd p, Ds " : ", Dd dom
        ,Ds "\nwe found this inconsistent with the current bindings:\n   "
        ,Df dbinds vs
        ,Ds "\nand equations:\n   "
        ,Df deqs truths
        ,Ds "\nBecause it requires solving: "
        ,Dl eqs ", "
        ,Ds "\nThis probably means this clause is unreachable code. "
        ,Ds (show n)
        ]}

deqs d xs = dispL f d xs ", "
  where f d (a,b) = (d1,x++"="++y) where (d1,x,y) = disp2 d (a,b)
dbinds d xs = dispL f d xs ", "
  where f d (a,(b,mod,_,_)) = (d1,x++":"++y) where (d1,x,y) = disp2 d (a,b)

pErr p moreps dom d1 mess =
  failDd "pErr" 2 d2 [Ds "While checking that the pattern: "
              ,Dd p, Ds " : ", Dn dom
              ,Ds (mess++postScript)]
 where (d2,morepsS) = dispL disp d1 moreps ","
       postScript = "\n(if this is a solving problem, perhaps the pattern might swap places "++
                    "\nwith one of the other patterns "++ morepsS++" which might establish the facts"++
                    "\nto prove the condition. Recall, facts accumulate from left to right.)"


-------------------------------------------------------------------
data Decs
-------------------------------------------------------------------
-- Checking that a data Dec is legal requires kind checking. If the data
-- Dec is parameterized we need to compute kinds for the parameters.
-- This can be done several ways.
-- 1) infer types        data T x y = C (x y)
-- 2) user annotations   data T (x :: * ~> *) (y :: *) = C (x y)
-- 3) use signtaure      T :: (* ~> *) ~> * ~> *
--                       data T x y = C (x y)
-- Once the parameters are processed, we use this information to
-- compute a kind for the type constructor (i.e. T above) and a Sigma
-- type for each of the constructor functions (i.e. C above), which
-- we check has kind *


-- compute information for each type constructor,
-- and each constructor function.
-- Then add theorems and rules, and build a Frag to return.

checkDataDecs :: Strata -> [Dec] -> TC (Sigma,Frag,[Dec])
checkDataDecs strata ds =
  do { (tmap,cmap) <- doManyData strata ds
     ; let propList = foldr isProp [] tmap -- Get list of props from mutRecDatas
           isProp (True,name,_,_) ps = name:ps
           isProp (False,name,_,_) ps = ps
     ; tmap2 <- mapM genTyCon tmap
     ; let f (nm,tau,polykind) = (nm,tau)
     ; cmap2 <- genConstrFunFrag (map f tmap2) (map snd cmap)
     ; let liftToTypeEnv (Global s,(sig,mod,n,exp)) = (s,TyCon (lv 1 {- TODO LEVEL -}) s (K sig),K sig)
           makeRule (isProp @ True,(Global c,(sigma,mod,_,_))) =
              do { r1 <- sigmaToRWrule Axiom c sigma
                 ; return [(rkey r1,r1)]}
           makeRule (False,(Global c,(sigma,mod,_,_))) = return []
           (types,values) =
             if strata == typeStrata
                then (tmap2,cmap2)
                else (map liftToTypeEnv cmap2 ++ tmap2,[])
     ; rules <- mapM makeRule cmap
     ; return(simpleSigma unitT,Frag values [] types [] [] (concat rules),ds)
     }

-- translate a [Pred] from a Maybe[Pred]
toPred env Nothing = return[]
toPred env (Just xs) = toEqs env xs


doManyData strata ds =
  do { envMap <- getTypeEnv

     ; (envMap2,tMap,cMap) <- checkDataBindingGroup ds envMap
     ; let f d (_,(var,(sigma,mod,_,_))) = displays d [Dd var,Ds ": ",Dd sigma]
           g d (_,var,sigma,poly) = displays d [Dd var,Ds ": ",Dd poly]
     -- ; warn [Ds "\nTemporary types:\n  ",Dlf g tMap "\n  "]
     -- ; whenD (not(null cMap)) [Ds "\nTemporary constructors:\n  ",Dlf f cMap "\n  "]

{-
     ; let proj (x,y,z) = (x,y)
     ; info <- mapM (dataBinds strata envMap) ds
     ; let acc (t,c) (ts,cs) = (t:ts,c++cs)
           (tMap,constrBinds) = foldr acc ([],[]) info
           project (isprop,name,sig,tau) = (name,sig,tau)
     ; let g (loc,isprop,name,allExParams,env2,eqs,body) =
             do { let env3 = (map project tMap)++ env2
                ; eqs2 <- toPred env3 eqs
                ; body2 <- toRho env3 body
                ; let typ = Forall (windup allExParams (eqs2,body2))
                ; newLoc loc $ hasKind name typ (MK (Star strata))
                ; typ2 <- zonk typ
                ; return(isprop,(Global name,(typ,0::Level,Var(Global name))))
                }
     ; cMap <- mapM g constrBinds
-}
     ; return (tMap,cMap)
     }


-- data T :: [forall (x:: k) . t] where ... ==> ([(x:: k)],t)
splitForall (Forallx All qs [] t) = return(qs,t)
splitForall (Forallx Ex _ _ _) = failD 2 [Ds "In GADT quantifier cannot be Exists"]
splitForall (Forallx _ _ (p:ps) _) = failD 2 [Ds "In GADT quantifier cannot have qualifications"]
splitForall k = return([],k)

newGADTnames (GADT loc strata b (Global tname) kind constrs) = freshNames badtypes
  where badtypes = kind : (TyVar' tname) : map g constrs
        g (loc,constr,prefix,preds,typ) = typ

matchArgsWithKinds (n:ns) (Karrow' x y) = (n,x,All): matchArgsWithKinds ns y
matchArgsWithKinds (n:ns) k = []

-- Con :: preds => typ
inferPrefix strata preds typ [] = map g vs
   where g nm = (nm,AnyTyp (strata +1),All)
         vs = nub(getFreePredL [] preds ++ getFree [] typ)
-- Con :: forall prefix . preds => typ
inferPrefix strata preds typ prefix =  map f prefix
   where f (nm,k) = (nm,k,All)

-- makeRangeEq [(a,k,q),(b,k2,q2),(c,k3,q3)] (T w x y) -->  (T a b c,[w=a,x=b,y=c])
makeRangeEq triples range = (f',zipWith h xs triples)
   where (t,xs) = root range [] -- (T,[w,x,y])
         f' = apply t triples   -- (T a b c)
         h x (nm,k,q) = Equality' (TyVar' nm) x
         apply f ((nm,k,q):xs) = apply (TyApp' f (TyVar' nm)) xs
         apply f [] = f
         root (TyApp' f x) args = root f (x:args)
         root t args = (t,args)


[u',v',w',x',y',z',a',b',c',d',e',f'] = map ty [1..12]
test34 = [(u',a'),(v',tlist b'),(w',a'),(x',c'),(y',b')]
Just zs = mguN test34
ty n = TcTv(Tv n (Rigid All Z (show n)) star)


-- when we have a range where a variable is mentioned twice
-- e.g.  (a -> [b] -> T a [b] a c b)  we get
--  [u=a,v=[b],w=a,x=c,y=b] => a -> [b] -> (T u v w x y)
-- we'd lke to simplify this to:
--  [a=u,[b]=v,a=w,c=x,b] => a -> [b] -> (T u v w x y)
--  [


arrowUp strata [] t = t
arrowUp 0 (x:xs) t = Rarrow' x (arrowUp 0 xs t)
arrowUp n (x:xs) t = Karrow' x (arrowUp n xs t)

-- compute typings and kindings from a Dec, they'll be checked later in "doManyData"
type ConType = (Loc,Bool,String,ForAllArgs,ToEnv, Maybe[PPred],PT)


-----------------------------------------------------------
-- New reworked style of computing things from Data decs

checkDataBindingGroup ds env =
  do { let getGADT (x@(Data _ _ _ _ _ _ _ _)) = data2gadt x
           getGADT (Explicit d) = return d
     ; gs <- mapM getGADT ds
     ; (env2,tDelta) <- typEnvForDataBindingGroup (map Explicit gs) env
     ; css <- mapM (constrType env2) gs
     ; return(env2,tDelta,concat css)
     }

{-  data2gadt translates from:

data T a b
  = C a (T a b)
  | D

To:

data T:: *0 ~> *0 ~> *0 where
  C:: forall (a:*0) (b:*0) . a -> T a b -> T a b
  D:: forall (a:*0) (b:*0) . T a b
-}

data2gadt (Data loc isP strat tname@(Global nm) hint args cs derivs) =
 do { (argBinds,rng) <- useSigToKindArgs strat args hint
    -- ([(a:*0),(b:*0)],*0)
    ; let name (nm,kind,quant) = nm
          proj (name,kind,quant) = (name,kind)
          range = applyT' (map TyVar' (nm : map name argBinds))
          -- T a b
          kind = foldr Karrow' rng (map (\(nm,pt,q)->pt) argBinds)
          -- *0 ~> *0 ~> *0
          each (Constr loc targs cname doms preds) =
               (loc,cname,map proj argBinds,some preds,arrowUp strat doms range)
          var (Global s) = s
          var (x@(Alpha _ _)) = show x
          some (Just xs) = xs
          some Nothing = []

    ; return(GADT loc strat isP tname kind (map each cs))
    }


badKind name tau d message =
  failD 3 [Ds "\nWhile checking the data declaration for: ",Ds name
          ,Ds "\nwe checked the well formedness of its kind: ",Dd tau
          ,Ds "\nAn error was found.\n",Ds message]

typEnvForDataBindingGroup:: [Dec] -> ToEnv -> TC(ToEnv,[(Bool,String,Tau,PolyKind)])
typEnvForDataBindingGroup ds env =
  do { info <- mapM kindOfTyConFromDec ds
     ; let addTyCon (isP,name,kind,level,loc) =
            do { (sigma,_) <- toSigma env kind
               ; sigma' <- newLoc loc $
                           handleM 3 (check sigma (Star (level + 1)))
                                     (badKind name kind)
               ; let kind = K sigma
               ; return(isP,name,TyCon (lv level) name kind,kind)}
           delProp (isP,nm,tau,poly) = (nm,tau,poly)
     ; delta <- mapM addTyCon info
     ; return (map delProp delta ++ env, delta)
     }

kindOfTyConFromDec (Explicit (GADT loc level isP (Global name) k cs)) =
  return(isP,name,k,level,loc)
kindOfTyConFromDec (Data loc isP level (Global name) (Just k) vs cs derivs) =
  return(isP,name,k,level,loc)
kindOfTyConFromDec (Data loc isP level (Global name) Nothing vs cs derivs) =
  do {(argBinds,rng) <- newLoc loc (useSigToKindArgs level vs Nothing)
     ; let tkindbody = foldr Karrow' rng (map (\(nm,pt,q)->pt) argBinds)
     ; return(isP,name,tkindbody,level,loc)}

-- The type environment currentMap already includes information for
-- all the type names in the mutually recursive binding group of GADTS.
-- We are just translating the constructors to Sigma types.

constrType :: [(String,Tau,PolyKind)] -> ExplicitGADT -> TC [(Bool,(Var,(Sigma,Mod,Level,Exp)))]
constrType currentMap (GADT loc level isProp tname tkind constrs) = mapM each constrs
  where each (loc,cname, vars, preds, typ) =
          do { (_,rng) <- checkRng cname tname level typ
             ; let bound = map (\ (nm,tau,kind) -> nm) currentMap
                   rngFree = getFree [] rng \\ bound
                   -- vars are Ex if they aren't in the range type
                   -- E.g. 'a' in   App:: Exp (a -> b) -> Exp a -> Exp b
                   -- except for: Eq:: forall (a:: *1) (b:: a) . Equal b b
                   quant (Star' _) n = All
                   quant _ n = if elem n rngFree then All else Ex
                   free = getFree [] typ `union` getFreePredL [] preds
             ; sigma <-
                 case vars of
                   -- The constr leaves the vars implicit.  C:: T a -> T a
                   [] -> do { let kind = AnyTyp (level+1)
                                  addQuant name = (name,kind,quant kind name)
                                  args = map addQuant (free \\ bound)
                            ; (nmMap,windupList,envMap) <- argsToEnv args currentMap
                            ; rho <- toRho envMap typ
                            ; ps <- toPred envMap (Just preds)
                            ; return (Forall(windup windupList (ps,rho)))}
                   -- The constr has explicit vars.  C:: foralll a . T a -> T a
                   _  -> do { let addQuant (name,kind) = (name,kind,quant kind name)
                                  quantVars = map addQuant vars
                                  sigmaPT = Forallx All quantVars preds typ
                            ; (sigma,nmMap) <- toSigma currentMap sigmaPT
                            ; return sigma}
             ; newLoc loc $
               handleM 3 (check sigma (Star level))
                         (illFormed cname sigma)
             ; sigma2 <- zonk sigma
             ; return(isProp,(cname,(sigma2,Rig,0,Var cname)))
             }


-- checkRng makes sure the range is the type being defined.
checkRng c tname 0 (Rarrow' d x) =
  do { (ds,r) <- checkRng c tname 0 x; return(d:ds,r) }
checkRng c tname 1 (Karrow' d x) =
  do { (ds,r) <- checkRng c tname 1 x; return (d:ds,r)}
checkRng c (Global tname) _ (t@(TyCon' nm)) | tname == nm = return ([],t)
checkRng c (Global tname) _ (t@(TyVar' nm)) | tname == nm = return ([],t)
checkRng c (Global tname) _ (t@(TyApp' _ _)) = down t
  where down (TyApp' (TyCon' s) x) | s==tname = return ([],t)
        down (TyApp' (TyVar' s) x) | s==tname = return ([],t)
        down (TyApp' x y) = down x
        down t = failD 2 [Ds "\nThe range of the constructor: ",Dd c
                         ,Ds " is not an application of: "
                         ,Dd tname,Ds ".\nInstead it is: ",Dd t,Ds(shtt t)]
checkRng c tname _ typ =
  failD 2 [Ds "\nThe range of the constructor: ",Dd c,Ds " is not "
          ,Dd tname,Ds ".\nInstead it is: ",Dd typ]



illFormed name rho d message =
  failD 3 [Ds "\nWhile checking the type of the constructor: ",Dd name
          ,Ds "\nwe checked the well-formedness of:\n  ",Dd rho
          ,Ds "\nAn error was found.\n",Ds message]

-----------------------------------------------------------------------

dataBinds:: Strata -> (ToEnv) -> Dec -> TC((Bool,String,Tau,PolyKind),[ConType])
dataBinds _ currentEnv (dd@(Explicit (x@(GADT loc strata isprop (Global tname) kind constrs)))) =
  do { -- showD [Ds ("Doing GADT "++tname)];
       case okGADT x of
         Just s -> failD 2 [Ds s]
         Nothing -> return ()
     ; (tkind,_) <- toSigma currentEnv kind
     -- ; newLoc loc $ hasKind tname tkind (MK (Star (strata + 1)))
     ; let tTau = TyCon (lv 1) tname (K tkind)
           tTrip = (tname,tTau,K tkind)
     ; (allTriples,kindBody) <- splitForall kind
     ; let fresh = newGADTnames x
           argTriples = matchArgsWithKinds fresh kindBody
           f d (str,pt) = displays d [Ds str,Ds ":: ",Dd pt]
     ; let doCon (loc,Global c,prefix,preds,typ) =
             do { let conTriples = inferPrefix strata preds typ prefix
                      trips = allTriples ++ argTriples ++ conTriples
                      (ts,rng) = getRange strata typ
                      (newrng,eqs) = makeRangeEq argTriples rng
                      ps = preds ++ eqs
                      ty = arrowUp strata ts newrng
                      swap (x,y) = (y,x)
                ; (strNamMap,forallargs,newEnv) <- argsToEnv trips currentEnv
                {-
                ; oldrangeTau <- toTau newEnv typ
                ; newrangeTau <- toTau newEnv rng
                ; newtypeTau <- toTau newEnv ty
                ; eqsPred <- toPred newEnv (Just eqs)
                ; warn [Ds "\n## ",Dd eqsPred , Ds " => ",Dd newtypeTau, Ds " | old = ",Dd newrangeTau]
                -}
                ; whenD False
                         [ Ds "\nalltrips = ",Dl allTriples", ",
                           Ds "\nargtrips = ",Dl argTriples ", ",
                           Ds "\ncontrips = ",Dl conTriples ", ",
                           Ds "\n***trips = ",Dl trips ", ",
                           Ds "\n forallargs = ",Dl forallargs "," ,
                           Ds "\n strNamMap = ", Dlf f strNamMap ", ",
                           Ds "\n preds = ",Dd preds,
                          Ds "\n eqs = ",Dd eqs,
                          Ds "\n ty = ",Dd ty]

                ; return((loc,isprop,c,forallargs,newEnv,Just ps,ty))}
     ; cs <- mapM doCon constrs
     ; return((isprop,tname,tTau,K tkind),cs)
     }
dataBinds strata currentEnv (dd@(Data loc isprop _ (t@(Global tname)) sig xs cs derivs)) =
  do { let (allArgs,eqs,hint) = sigToForallParts strata sig
     -- ; showD [Ds "\nIn dataBinds\nData = \n ", Ds (show dd)]

     ; if null eqs then return ()
                   else failD 2 [Ds "data signature cannot have equations: ",Dl eqs ", "]
     ; (_,allParams,allEnv) <- argsToEnv allArgs currentEnv
     ; (argBinds,rng) <- newLoc loc (useSigToKindArgs strata xs hint)
     ; (_,argParams,argEnv) <- argsToEnv argBinds allEnv
     ; let tkindbody = foldr Karrow' rng (map (\(nm,pt,q)->pt) argBinds)
           tType = TyCon' tname
           var (s,k,q) = TyVar' s
           rngType = applyT' (tType : map var argBinds)
     ; cTypes <- mapM (conType isprop strata (allParams ++argParams) argEnv rngType) cs
     ; rho <- toRho argEnv {- allEnv -} tkindbody
     ; tkind <- return (K(Forall (windup allParams ([],rho))))
     ; return((isprop,tname,TyCon (lv 1 {- TODO LEVEL -}) tname tkind,tkind),cTypes) }


conType :: Bool -> Strata -> ForAllArgs -> (ToEnv) -> PT -> Constr -> TC ConType
conType isprop strata allParams allEnv rng (cc@(Constr loc exs c@(Global cname) ts eqs)) =
    do { -- warn [Ds "Constr= ",Dd cc,Ds " range = ",Dd rng];
       (_,exParams,allExEnv) <- argsToEnv (map f exs) allEnv
       ; return(loc,isprop,cname,allParams ++ exParams,allExEnv,eqs,cbody) }
  where f (Global s,k) = (s,k,qual s)
        rangevs = rangeVars rng (case eqs of {Just xs -> xs; Nothing -> []})
        qual s = if elem s rangevs then All else Ex
        cbody = foldr arr rng ts
        arr = (if strata == typeStrata then Rarrow' else Karrow')


rangeVars newrange quals = nub(concat(map f vs)++vs)
  where vs = getFree [] newrange
        find v [] = Nothing
        find v ((Equality' (TyVar' s) t):xs) | v==s = Just t
        find v (x:xs) = find v xs
        f v = case find v quals of
                Nothing -> [v]
                Just t -> getFree [] t


-- A signature can have several forms
-- 1) It can be missing
-- 2) T :: a ~> b ~> *
-- 3) T :: forall a b . a ~> b ~> *
-- 4) T :: forall a b . (a=b,c=d) => a ~> b ~> *
-- We want to split it into its parts ([a,b],[(a=b),(c=d)],a ~> b ~> * )

sigToForallParts strata Nothing = ([],[],Nothing)
sigToForallParts strata (Just (Forallx q binds eqs t)) = (binds,eqs,Just t)
sigToForallParts strata (Just t) = (map f (getFree [] t),[],Just t)
  where f s = (s,(Star' (strata + 1)),All)

-- Given T :: a ~> b ~> * ; data T x y = ... OR data T (x:a) (y:b) = ...
-- Bind the args to their kinds [(x,a),(y,b)]. If there is No kind
-- information, use default rules, which depend om the strata information

useSigToKindArgs::Strata-> [(Var,PT)]-> Maybe PT->TC([(String,PT,Quant)],PT)
useSigToKindArgs strata args sig = walk args sig where
  walk [] Nothing = return ([],Star' strata)     -- implicit (T a b):: *
  walk zs (Just (Forallx _ ps _ z)) =
       do { (qs,t) <- walk zs (Just z)
          ; warn [Ds "In walk, ps = ",Dl ps ","]
          ; return(ps ++ qs,t) }
  walk [] (Just (Star' n))
        -- | n == strata
        = return ([],Star' n) -- explicit (T a b):: *
  walk [] (Just t) = failD 2 [Ds "Explict kinding for new type must result in kind *0, not ",Dd t]
  walk ((Global v,AnyTyp n):vs) Nothing =
    do { (xs,rng) <- walk vs Nothing
       ; return((v,AnyTyp n,All):xs,rng) }
  walk ((Global v,AnyTyp _):vs) (Just(Karrow' d r)) =
    do { (xs,rng) <- walk vs (Just r)
       ; return((v,d,All):xs,rng) }
  walk ((Global v,d):vs) Nothing =
    do { (xs,rng) <- walk vs Nothing
       ; return((v,d,All):xs,rng) }
  walk ((Global v,d1):vs) (Just (Karrow' d2 r)) =
    if True  -- samePT d1 d2 -- Prefer given?
       then do { (xs,rng) <- walk vs (Just r)
               ; return((v,d2,All):xs,rng)
               }
       else failD 2 [Ds "data Dec has explicit signature and explicit kindings on arguments, "
                    ,Ds "but they don't match. "
                    ,Dd d1, Ds " != ",Dd d2]
  walk (v:vs) (Just t) = failD 2 [Ds "Expecting kind arrow like (a ~> b), found: ",Dd t]


genConstrFunFrag tyConSub xs = mapM f xs where
  f (nm,(sig,mod,lev,exp)) =
    do { -- Replace TyCon's which have stale (i.e. mono) PolyKind fields
         sig1 <- sub ([],[],tyConSub,[]) sig -- TODO LEVEL
       ; sig3 <- generalize sig1  -- Now generalize
       ; return(nm,(sig3,mod,lev,exp))}

genTyCon :: (Bool,String,Tau,PolyKind) -> TC (String,Tau,PolyKind)
genTyCon (isprop,nm,TyCon level_ _ _,K k) =
  do { k2 <- generalize k
     ; return(nm,TyCon level_ nm (K k2),K k2) }

------------------------------------------------------------------------
-- Fun and Val Decs
------------------------------------------------------------------------

isValFunPat (Val _ _ _ _) = True
isValFunPat (Fun _ _ _ _) = True
isValFunPat (Pat _ _ _ _) = True
isValFunPat (TypeSig _ _ _) = True
isValFunPat (Reject s d) = True
isValFunPat (Prim l n t) = True
isValFunPat _ = False

displayFragElem  (nm,(sig,lev,exp)) = outputString (show nm++" : "++show sig++"\n")

inferBndrForDecs :: Bool -> [Dec] -> TC (Frag,[Dec])
inferBndrForDecs renam ds = many dss
  where (dss,pairs) = topSortR freeOfDec ds
        many [] =  return(nullFrag,[])
        many (ds:dss) =
           do { (_,frag1,xs) <- inferBndr renam nullFrag ds
              ; let names = concat(map decname ds)
                    (_,message) = displays disp0 [Ds"The binding group: ",Dl names ","]
              ; (frag2,ys) <- underLet (message,starR) frag1 (many dss)
              ; frag3 <- frag2 +++ frag1
              ; return (frag3,xs++ys)}


instance TypableBinder [Dec] where
  inferBndr renm k [] = return(simpleSigma unitT,k,[])
  inferBndr renm k ds | all isTheorem ds =
    do { let f (AddTheorem xs) = xs
             xs = concat(map f ds)
       ; env <- tcEnv
       ; theorems <- computeTheorems xs env
       ; return(simpleSigma unitT,addRules theorems k,[])  -- erase theorems
       }
  inferBndr renm frag1 ds | all isValFunPat ds =
    do { let decs = useTypeSig ds
       ; (frag2,triples) <- getDecTyp renm decs -- Step 1
       ; frag3 <-  frag2 +++ frag1
       ; ds2 <- mapM (checkDec frag3) triples -- Step 2
       ; frag4 <- genFrag frag3
       ; return(simpleSigma unitT,frag4,ds2)
       }
  inferBndr rename frag ds = failD 2 [Ds "\nMixup in Decs\n", Ds (show ds)]
  checkBndr rename mod k sigma ds = error "Can't checkBndr a [Dec]"

-- Step 1. Compute just the "frag" for the decls. Don't do their bodies yet.

getDecTyp :: Bool -> [Dec] -> TC (Frag,[([(Z,String)],Mod,Rho,Dec,[Pred],[TcTv])])
getDecTyp rename [] = return(nullFrag,[])
getDecTyp rename (d:ds) =
  do { (disp,frag1,mod,rho,d,eqns,skols) <- getOneDec rename d
     ; (frag2,triples) <- getDecTyp rename ds
     ; frag3 <- frag2 +++ frag1
     ; return(frag3,(disp,mod,rho,d,eqns,skols):triples) }


guess (Normal exp) = handleM 5
  (do { dom <- newTau star
      ; e2 <- typeExp Wob exp (Check(Rtau dom))
      ; (dom2,mod2) <- rigidity dom
      ; return mod2}) (\ _ _ -> return Wob)
guess x = return Wob

getOneDec rename (d@(Val loc (Pann pat pt) body ds)) = newLoc loc $
  do { (sigma,(d1,rho,assump,skol)) <- checkPT pt    -- use the hint to get rho and display
     ; (frag,pat2) <- checkBndr rename Rig nullFrag sigma pat
     ; frag2 <- addTheorem (show pat) frag sigma
     ; return(d1,addSkol skol frag2,Rig,rho,Val loc pat2 body ds,assump,skol)}
getOneDec rename (Val loc pat body ds) = newLoc loc $
  do { (sigma,frag,pat2) <- inferBndr rename nullFrag pat
     ; (rigid,assump,rho) <- rigidTy Ex loc (show pat) sigma
     -- Smart Let from "Simple Unification Based Type Inference for GADTS"
     ; mod <- guess body
     ; return([],frag,mod,rho,Val loc pat2 body ds,assump,[])}
getOneDec rename (Fun loc nm Nothing ms) = newLoc loc $
  do { sigma <- newSigma star
     ; (frag,nm2) <- checkBndr rename Wob nullFrag sigma nm
     ; (rigid,assump,rho) <- rigidTy Ex loc (show nm) sigma
     ; r1 <- zonk rho
     ; return([],frag,Wob,rho,Fun loc nm2 Nothing ms,assump,[])}
getOneDec rename (Fun loc (nm@(Global fname)) (Just pt) ms) = newLoc loc $
  do { (sigma,(d1,rho,assump,skol)) <- checkPT pt -- use the hint to get rho and display
     ; (frag,nm2) <- setDisplay (newDI d1) (checkBndr rename Rig nullFrag sigma nm)
     ; r1 <- zonk rho
     ; frag2 <- addTheorem fname frag sigma
     ; return(d1,addSkol skol frag2,Rig,r1,Fun loc nm2 (Just pt) ms,assump,skol)}
getOneDec rename (Pat loc nm vs p) = newLoc loc $
  do { (sigma,frag,nm2) <- inferBndr rename nullFrag nm
     ; (rigid,assump,rho) <- rigidTy Ex loc (show nm) sigma
     ; return([],frag,Wob,rho,Pat loc nm2 vs p,assump,[])}
getOneDec rename (Reject s ds) = return ([],nullFrag,Wob,Rtau unitT,Reject s ds,[],[])
getOneDec rename (Prim l nm t) =
  do { (sigma,frag,_) <- inferBndr rename nullFrag (Pann (Pvar nm) t)
     ; return([],frag,Wob,error "Shouldn't Check Prim type",Prim l nm t,[],[]) }
getOneDec rename d = failD 2 [Ds "Illegal dec in value binding group: ",Ds (show d)]

-- rigidTy is called when checking the body of a Dec with an explicit
-- type signature. It replaces all type variables with kinds classified
-- by *1 (i.e. *0 or other kinds classified by *1) with
-- new rigid type variables. For example a type like
-- (forall (k:*1) (u:k) a . (AtomX u) -> a -> Pair)
-- should rigidify "u" and "a", but not "k"

rigidTy :: TyCh m => Quant -> Loc -> String -> Sigma -> m([TcTv],[Pred],Rho)
rigidTy q loc s sigma = unBindWith (newRigid loc s) sigma


-- Step 2. Compute the bodies. All the names being bound are
-- already in the frag passed as input.

chMs [] rho = return []
chMs (m:ms) rho = do { m1 <- (check m rho)
                     ; m1s <- chMs ms rho; return(m1:m1s)}

bodyName pat (Normal e) = show e
bodyName pat (Guarded _) = "guarded pattern: "++show pat
bodyName pat Unreachable = "unreachable"

unequalArities ms = not(same(map arity ms))
  where arity (loc,ps,body,ds) = length ps
        same [] = True
        same [x] = True
        same (x:y:zs) | x==y = same (y:zs)
        same _ = False

checkDec :: Frag -> ([(Z,String)],Mod,Rho,Dec,[Pred],[TcTv]) -> TC Dec
checkDec frag (d1,mod,rho,Val loc pat body ds,eqns,skols) = newLoc loc $
  do { let lhsString = bodyName pat body
     ; (frag2,ds2) <- inferBndrForDecs localRename ds
     -- ; (preds,unifier) <- fragMGU ("Checking where clause of "++show pat,starR) frag2
     ; frag3 <- addPred eqns frag
     ; ((assump,body2),oblig) <-
           collectPred
           (underLetGetPred (lhsString,rho) (addSkol skols frag3)
           (lambdaExtend frag2
           (setDisplay (newDI d1) (typeBody mod body (Check rho)))))
     ; truths <- getAssume
     ; oblig2 <- solveConstraints (lhsString,rho) (assump++truths) oblig
     ; when (not (null oblig2))
            (do { r <- refutable oblig2
                ; failD 3 [Ds "\nWhile type checking: ", Dd pat
                     ,Ds "\nUnder the truths: "
                     ,Dl (assump++truths) ", "
                     ,Ds "\nWe tried to solve: "
                     ,Dl oblig ","
                     ,Ds "\nBut we were left with: "
                     ,Dl oblig2 ", ",r]})
     ; return(Val loc pat body2 ds2) }

checkDec frag (d1,mod,rho,Fun loc nm hint ms,eqns,skols) | unequalArities ms =
  failD 3 [Ds ("\n\nThe equations for function: "++show nm++", give different aritites.")]
checkDec frag (d1,mod,rho,Fun loc nm hint ms,eqns,skols) = newLoc loc $
  do { frag3 <- addPred eqns frag
     --FIX; showFrag (show nm) frag3
     --; let d2 = newDI d1
     --; d3 <- warnD d2 [Ds ("\n\n"++show nm),Ds "\nRho = ",Dd rho
     --           ,Ds "\n  skol = ",Dl skols  ", "
     --           ,Ds (plistf (shtt . TcTv) "(" skols ", " ")")]


     ; let hasRho (loc,ps,bod,ds) = typeMatchPs mod (show nm,loc,ps,bod,ds) (Check rho)
           stripName (nm,loc,ps,bod,ds) = (loc,ps,bod,ds)
     ; ((assump,ms2),oblig) <-
           collectPred
           (underLamGetPred frag3 (show nm,rho)
           (setDisplay (newDI d1) (mapM hasRho ms)))
     --; warnD d3 [Ds "\nassump =",Dd assump,Ds "\n oblig = ",Dd oblig]
     ; truths <- getAssume
     --; warn [Ds "\nGetting ready to solve for ",Ds (show nm),Ds "\n"]
     ; oblig2 <- solveConstraints (show nm,rho) (assump++truths) oblig
     ; when (not (null oblig2))
                 (failD 3
                   [Ds ("\nWhile type checking: "++show nm)
                   ,Ds "\nUnder the truths: "
                   ,Dl (assump++truths) ", "
                   ,Ds "\nWe tried to solve: "
                   ,Dl oblig ", "
                   ,Ds "\nBut we were left with: "
                   ,Dl oblig2 ", "])
     ; return(Fun loc nm hint (map stripName ms2)) }
checkDec frag (d1,mod,rho,Pat loc nm vs p,eqns,skols) = newLoc loc $
  do { frag3 <- addPred eqns frag
     -- ; (preds,unifier) <- fragMGU ("Checking "++show nm,starR) frag3
     ; (Forall (Nil (assump,ty)),(Frag xs tvs tenv eqs theta rs),p2)
               <- lambdaExtend frag3 (inferBndr False nullFrag p)
     ; argtys <- compareL vs xs
     ; morepoly (show nm) (foldr arrow ty argtys) rho
     ; return(Pat loc nm vs p2)
     }

checkDec frag (d1,mod,rho,Reject s ds,eqns,skols) =
  handleM 7 (do { (frag2,ds2) <- inferBndrForDecs localRename ds
                ; fail ("\nReject test: "++s++" did not fail.")}) errF
 where errF dis _= do { outputString ("\n*** negative test '"++ s ++
                                  "' fails as expected\n")
                  ; return (TypeSig Z (Global "##test") tunit')}
checkDec frag (d1,mod,_,Prim loc nm t,eqns,skols) = newLoc loc $ return(Prim loc nm t)
checkDec frag (d1,mod,rho,t,eqns,skols) = failD 2 [Ds "Illegal dec in value binding group: ", Ds (show d1)]

----------------
-- Helper functions for typing [Dec]

-- Generalize a Frag after type inference

genFrag (Frag xs ys tenv eqs theta rs ) =
     do { zs <- mapM gen xs; return(Frag zs ys tenv eqs theta rs )}
  where gen (var,(sigma@(Forall (Nil b)),mod,level,exp)) =
            do { s1 <- zonk sigma
               ; s2 <- generalize b; return (var,(s2,mod,level,exp))}
        gen (var,(sigma,mod,level,exp)) =
            do { s2 <- zonk sigma; return(var,(s2,mod,level,exp)) }


-- Compare that all the vars in a pattern Dec are used

compareL :: TyCh m => [Var] -> [(Var,(ty,Mod,Level,exp))] -> m [ty]
compareL xs fs =
    do { tys <- mapM get xs
       ; when (not ((length xs) == (length fs)))
              (failD 2 [Ds "Unknown var in pattern."])
       ; return tys }
  where get x = case lookup x fs of
                  Nothing -> failD 2 [Ds "Unused formal parameter: ",Dd x]
                  Just (ty,mod,_,_) -> return ty

-- Generate a reasonable error message when Skolem vars escape

escapes :: TyCh m =>  DispInfo Z -> [(String,Sigma,[TcTv])] -> [TcTv] -> m ()
escapes d0 trips [] = return ()
escapes d0 trips bad = do { as <- getBindings
                       ; (display,lines) <- foldrM (f as) (d0,"") bad
                       ; failDd "escapes" 2 display [Ds lines] }
  where f as (v@(Tv _ (Rigid All loc s) k)) (d1,str) =
           (do { (d2,typing) <- get d1 v trips
               ; let elements = [Ds "The prototype gives a type where the variable: "
                                ,Ds s,Ds " is polymorphic.\nBut, this is not the case. "
                                ,Ds "The context demands the typing ",Ds (typing++".")]
               ; return(displays d2 elements)})
        f as (v@(Tv _ (Rigid Ex loc s) k)) (d1,str) =
          do { (d2,var) <- get d1 v trips
             ; return $
                displays d2
                  [Ds "\nAn existential type var: ", Dd v
                  ,Ds ("\narising from the pattern: "++s)
                  ,Ds (" at "++show loc)
                  ,Ds "\nescapes into the environment in the type of ",Dd var]}
        get d1 v [] = return (d1,"?")
        get d1 v ((name,typ,vs):xs) =
            do { t <- zonk typ
               ; if v `elem` vs
                    then return(displays d1 [Ds name,Ds ":: ",Dd t])
                    else get d1 v xs }

escapeCheck :: (TyCh m,Show a) => a -> Rho -> Frag -> m ()
escapeCheck term typ (Frag _ skolvars _ _ _ _) =
 do { (resultVars, level_) <- get_tvs typ
    ; let bad = filter (`elem` resultVars) skolvars
    ; when (not (null bad))
           (escapes disp0 [("the exp\n   "++show term,(Forall (Nil([],typ))),bad)] bad)
    }


skolFrag (Frag _ skolvars _ _ _ _) = skolvars
-----------------------------------------------------------------

fragMGU :: (String,Rho) -> Frag -> TC([Pred],MGU)  -- FIX THETA
fragMGU (name,rho) (Frag _ _ _ eqs theta rs) = handleM 3 (mguM ("7."++name,rho) eqs) err
  where err d1 mess = failDd "mguErr" 2 d1
               [Ds mess
               ,Ds "\nThe patterns: "
               ,Ds name
               ,Ds "\nmay have inconsistent types, indicating unreachable code."]

underLet :: (String,Rho) -> Frag -> TC a -> TC a
underLet s frag x = do { (_,ans) <- underLetGetPred s frag x; return ans}

underLam :: Frag -> (String,Rho) -> TC a -> TC a
underLam frag p x = do { (_,ans) <- underLamGetPred frag p x; return ans}

underLamGetPred :: Frag -> (String,Rho) -> TC a -> TC([Pred], a)
underLamGetPred frag p@(nm,rho) x =
   do { frag2 <- zonk frag
      --; (preds,unifier) <- fragMGU p frag2
      --; showFrag "In underLamGetPred2" frag2
      --; warn [Ds ("Under Lam at "++p++"\npreds = "),Dl preds "; ",Ds "\nunifier = ", Dd unifier]
      ; (ans,preds) <- extractAccum (under (lambdaExtend) p frag2 x)
      ; return(preds,ans) }


underLetGetPred :: (String,Rho) -> Frag -> TC a -> TC([Pred],a)
underLetGetPred s@(nm,rho) frag x =
  do { --(preds,unifier) <- fragMGU s frag;
       (ans,preds) <- extractAccum (under letExtend s frag x)
     ; return(preds,ans)
     }

prefix [] xs = True
prefix (x:xs) (y:ys) | x==y = prefix xs ys
prefix _ _ = False


underErr1 patvars (d1@(DI (pairs,_))) message = failP "underErr1" 3 d1 newmessage
  where bad = concat [ match dispv patv | dispv <- pairs, patv <- patvars]
        --match (m,freshname) (Tv n (Rigid Ex loc s) k) | m==n = [(freshname,loc,s)]
        match (ZTv (Tv m flav k),freshname) (Tv n (Rigid Ex loc s) k2)
              | m==n = [(freshname,loc,s)]
        match _ _ = []
        newmessage = message ++ concat(map report bad)
        report (name,loc,s) =
           "\nAn existential type var: "++name++
           "\n  arising from the pattern: "++s++" at "++show loc++" escapes"

getVarsFromEnv = do { env <- getGenerics; foldrM f ([],[]) env }
  where f (name,typ) (vars,trips) =
          do { (vs, level_) <- get_tvs typ
             ; if null vs
                  then return (vars,trips)
                  else return(vs++vars,(show name,typ,vs):trips) }

badUse unifier eqs = test bad
   where bad = [(v,old,new) | (v,old) <- eqs, (u,new) <- unifier, u==v]
         test [] = return ()
         test ((v,old,new):more) | old /= new =
            failD 3 [Ds "The type variable: ",Dd v,Ds " is used in a context that reqires it to be "
                     ,Dd new,Ds ".\nThe functions declared type is too general."]
         test (m:more) = test more

-- HERE ###  -- FIX THETA
under :: (Frag -> b -> TC c) -> (String,Rho) -> Frag -> b -> TC c
under extend (p@(nm,rho)) frag comp =
  do { frag2@(Frag xs patVars tenv eqs theta rs) <- zonk frag
     -- This is where everything happens, the rest of the code
     -- just deals with the consequences.
     ; (answer,collected) <- handleM 3 (collectPred(extend frag2 comp))
                                       (underErr1 patVars)

     ; let pf (Equality _ _) = True
           pf (EqAssump _ _) = True
           pf _ = False
           (oblig,residual) = partition pf collected
     ; assump <- getTruths  -- Truths we already know, "eqs" are truths we will add
     ; un <- getBindings
     ; d1 <- getDisplay
     ; theta2 <- zonk theta
     ; eqs2 <- zonk eqs
     ; d2 <- whenDd False d1
              [Ds "\nTheta = ",Dl (theta2 ++ un) ", "
              ,Ds "\nTruths = ",Dl (eqs2 ++ assump) "; "
              ,Ds "\nObligations = ", Dl oblig "; "]
     ;
     -- First try and discharge the obligations incurred

     ; unifier <- handleM 1
                  (solveByNarrowing (3,25) ("7."++nm,rho)
                                    (eqs2 ++ assump) (map pred2Pair oblig))
                  (underErr frag nm assump oblig)

     -- ; (residual,unifier) <- handleM 1 (setTruths eqs (mguM ("8."++nm,rho) oblig))
     --                                   (underErr frag nm assump oblig)

     ; u2 <- zonk unifier

     -- The unifier obtained by solving the obligations must be
     -- consistent with the bindings in the Type Checking Env.
     -- These come either from a prototype, or a GADT constructor.
     -- If they're not consistent then the function less
     -- general then the user declared.

     ; let acc (Equality (TcTv x) tau) ans = (x,tau):ans
           acc (Equality tau (TcTv x)) ans = (x,tau):ans
           acc x ans = ans
     ; whenDd False d1
            [Ds "In under u2 = ",Dl u2 ", "
            ,Ds "\neqs = ",Dl eqs ", "
            ,Ds "\n obligation = ",Dd oblig,Ds "\nresidual = ",Dd residual
            ,Ds "\nThe skolem vars are: ",Dl patVars ";  ",Ds "\n"]
     ; badUse u2 (foldr acc [] eqs)

     -- if one of the variables bound in the unifier is a RigidVar
     -- that is mentioned in the Equalities, then the term is not
     -- as polymorphic as required.

     ; (free,_) <- get_tvs eqs
     ; let rigid (Tv u (Rigid _ _ _) k) = True
           rigid _ = False
     ; bad_rigid u2 (filter rigid free)


     ; d1 <- whenDd False disp0    --FIX
                  [Ds ("\nunder "++nm)
                  ,Ds "\noblig = ", Dd oblig
                  ,Ds "\nresidual = ", Dd residual
                  ,Ds "\nunifier = ", Dd u2 -- unifier
                  ,Ds "\neqs = ",Dd eqs
                  ,Ds "\nassump = ",Dd assump
                  ,Ds "\nskolvars = ",Dl patVars ","]
     ; let truths = (eqs++assump)
     ; unsolved <- solveConstraints p truths residual
     ; (bad,passOn) <- splitObligations unsolved patVars
     ; when (not (null bad))
            (failD 2
              [Ds "\nIn the scope of the patterns: ",Ds nm
              ,Ds "\nUnder the assumptions:\n   "
              ,Dl truths ", "
              ,Ds "\nWe could not solve the obligations:\n   "
              ,Dl residual ", "
              ,Ds "\nBecause after simplification we were left with:\n   "
              ,Dl bad ", "])
     ; (envVars,envTrip) <- getVarsFromEnv
     ; let (uVars,uTrip) = (map fst unifier,uInfo unifier)
           vars = envVars ++ uVars
           triples = envTrip ++ uTrip
     ; let bad = nub(filter (`elem` vars) patVars)
     ; when (not (null bad)) (escapes d1 triples bad)
     ; injectAccum passOn
     ; return answer
     }

bad_rigid [] free = return ()
bad_rigid ((v,term):more) free =
   case find (== v) free of
     Just (x@(Tv u (Rigid q loc info) k)) ->
        failD 3 [Ds "The type variable ",Dd x,Ds " is not polymorphic as declared."
                ,Ds "\nContext requires that it have type ",Dd term,Ds ".\n"]
     Nothing -> bad_rigid more free



-- The bindings in a unifier are turned into a triples data structure.
-- This helps make better error reporting. A triple binds the name
-- used in the source file, with the type it is bound to in the unifier.
uInfo unifier = map f unifier
  where f (v,tau) = (name v,simpleSigma tau,[v])
        name (Tv _ (Rigid All loc s) k) = s
        name v = show v

gg d (x,y,z) = displays d [Ds "(",Dd x,Ds ",",Dd y,Ds ",[",Dl z ",",Ds "])"]


underErr frag pat assump oblig info s =
   -- showFrag "UnderErr" frag >>
   failDd "underErr" 2 info
     [Ds ("\nWhile type checking in the scope of\n   "++pat)
     ,Ds "\nWe need to prove\n   ",Dd oblig
     ,Ds  "\nFrom the bindings\n   ", Dd assump
     ,Ds "\nBut ",Ds s]


splitObligations :: [Pred] -> [TcTv] -> TC([Pred],[Pred])
splitObligations need patVars = do { xs <- mapM f need; return(split xs ([],[])) }
  where f x = do { (vs, level_) <- get_tvs x; return (x,vs) }
        split [] pair = pair
        split ((x,vs):xs) (yes,no) =
           split xs (if any (`elem` patVars) vs then (x:yes,no) else (yes,x:no))

--------------------------------------------------------------------------

peek :: TC a -> TC (a,[Pred])
peek x = do { (a,eqs) <- collectPred x; injectAccum eqs; return(a,eqs) }

instance Typable (Mtc Z TcEnv Pred) (Body Exp) Rho where
  tc = typeBody Wob

typeBody :: Mod -> Body Exp -> (Expected Rho) -> TC(Body Exp)
typeBody mod (Normal e) expect =
     do { e' <- typeExp mod e expect
        ; return(Normal e')}
typeBody mod (Guarded xs) expect = do { xs' <- mapM f xs; return(Guarded xs')}
     where f (test,body) =
             binaryLift(,)(typeExp Rig test (Check(Rtau boolT)))
                          (typeExp mod body expect)
typeBody mod Unreachable expect = failD 3 [Ds "No Unreaachable Yet 1"]

------------------------------------------------------------------
-- This instance useable for (Fun matches)
-- f :: d1 -> d2 -> rng
-- f p1 p2 = e    leads to a call like:
-- tc (line 1, [p1,p2],Normal e,[]) (Check (d1 -> d2 -> rng))

-- ###

matchContext ps body = bodyName (Pvar (Global ("match: "++show ps))) body

mContxt loc nm ps body =
  "\n"++show loc++"\n"++nm++plist " " ps " " " = "++take 10 (show body)++ "..."
wContxt loc nm ps =
  "\n"++show loc++"\n"++nm++plist " " ps " " " = ... where ds"

typeMatchPs:: Mod -> (String,Loc,[Pat],Body Exp,[Dec]) -> Expected Rho -> TC(String,Loc,[Pat],Body Exp,[Dec])
typeMatchPs mod (x@(nm,loc,ps,Unreachable,ds)) (Check t) = newLoc loc $
      do { let good disp message = return x
               bad = failD 3 [Ds "The patterns: ",Dl ps ", ",Ds "  do not guard unreachable code."]
         ; truths <- collectEqAssump
         ; handleK (=="mguErr") 3 (checkBndrs True Rig nullFrag ps t >> bad) good }
typeMatchPs mod (nm,loc,ps,body,ds) (Check t) = newLoc loc $
     do { (frag1,ps1,rng) <- checkBndrs localRename mod nullFrag ps t
        ; t11 <- zonk t
        ; d1 <- getDisplay
        ; let err dis s  =
               (do { (Frag zs _ _ ts theta rs) <- zonk frag1
                   ; truths <- getBindings
                   ; failDd "tcMatch[Pat]" 3 dis
                       [Ds "\n*** Error in clause: "
                       ,Dl ps " ",Ds " = ",Ds (show body), Ds ":\n    ",Dd t
                       ,Ds "\n*** with\n   ",Dlf dispBind zs ", "
                       ,Ds "\n*** where ", Dl (subPred truths ts) ", "
                       ,Ds s]} )

        ; (frag2,ds2) <- underLam frag1 (wContxt loc nm ps,starR)
                                   (inferBndrForDecs localRename ds)
        ; let context = mContxt loc nm ps body
              rng2 = subRho (getTheta frag1) rng
        ; body3 <- handleM 2 (underLet ("XX "++context,starR) frag2
                             (underLam frag1 (context,rng)
                                      (chBody1 mod frag1 d1 body rng2)))
                             err
        ; escapeCheck body t frag1
        ; return(nm,loc,ps1,body3,ds2) }

typeMatchPs mod (nm,loc,ps,body,ds) (Infer ref) = newLoc loc $
     do { (ts,frag1,ps1) <- inferBndrs localRename nullFrag ps
        ; let context = (matchContext ps body,starR)
        ; (frag2,ds2) <- underLam frag1 ("where ...",starR)
                                    (inferBndrForDecs localRename ds)
        ; (rng,body3) <- (underLet context frag2
                         (underLam frag1 context (infer body)))
        -- ESCAPE CHECK
        ; escapeCheck body rng frag1
        ; let t = foldr arrow rng ts
        ; writeRef ref t
        ; return(nm,loc,ps1,body3,ds2) }

chBody1 mod frag d1 body rng =
  do { let verbose = False
           vs = (getTermVars frag)
           xs = skolFrag frag
     ; d5 <-
          if verbose
             then (do { d2 <- warnD d1 [Ds ("\n*****************\nChecking clause: "++show body)
                                       ,Ds ("\nhas the type:    "),Dd rng
                                       ,Ds "\nIn the scope of vars:"
                                       ,Ds "\nskolem vars: ",Dl xs ", "
                                       ,Ds "\nmode = ",Dd mod]
                      ; d3 <- showVals d2 (map show vs)
                      ; d4 <- showBindings d3
                      ; showAssumptions d4})
            else (return d1)
     ; (ans,ps) <- peek (inDisplay d5 (typeBody mod body (Check rng)))
     ; rng2 <- zonk rng
     ; whenDd verbose d5 [Ds "The preds generated = ",Dl ps "; "
                         ,Ds "\nThe range type computed ",Dd rng2]
     ; return ans
     }

                                 -- (Match [Pat] Exp Dec)
instance Typable (Mtc Z TcEnv Pred) (String,Loc,[Pat],Body Exp,[Dec]) Rho where
  tc = typeMatchPs Wob


showSome xs =
 do { let getenv = (Tc (\ x -> return(x,[])))
          p (Global x,_) = x `elem` xs
    ; env <- getenv
    ; showSomeVals p env
    }

-----------------------------------------------------------
-- This instance useable for (Case matches)
-- case e of { (C p1 p2) -> e }    leads to a call like
-- tc (line 1,(C p1 p2),Normal e,[]) expected

typeMatch:: Mod -> Match Pat Exp Dec -> Expected Rho -> TC (Match Pat Exp Dec)
typeMatch mod (x@(loc,p,Unreachable,ds)) (Check t) =
      do { (dom,rng) <- unifyFun t
         ; let good disp message = return x
               bad = failD 3 [Ds "The pattern: ",Dd p,Ds " does not guard unreachable code."]
               action = do { (frag,p1) <- checkBndr True Rig nullFrag dom p
                           ; fragMGU ("Unreachable",sigmaRho dom) frag}
         ; handleK (=="mguErr") 3 (action >> bad) good }
typeMatch mod (loc,p,body,ds) (Check t) = newLoc loc $
     do { ((dom,rng),obs) <- collectPred (unifyFun t)
        ; (frag1,p1) <- checkBndr localRename mod nullFrag dom p
        ; frag99 <- zonk frag1
        -- ; showFrag ("\nUnder pat: "++show p++": "++show dom) frag99
        ; let err dis s  =
               (do { (Frag zs _ _ truths theta rs) <- zonk frag1
                   ; binds <- getBindings
                   ; failDd "tcMatchPat" 2 dis
                      [Ds "\n*** Error type checking match ***"
                      ,Ds ("\n*** clause: " ++show p++" -> "++show body)
                      ,Ds  "\n***   type: ",Dd t
                      ,Ds  "\n***   vars: ",Dlf dispBind zs ", "
                      ,Ds  "\n*** truths: ",Dl (subPred binds truths) ", "
                      ,Ds ("\n"++s)]})
        -- compute binding info from where clause
        ; (frag2,ds2) <- underLam frag99 ("where ...",starR)
                                        (inferBndrForDecs localRename ds)
        -- check the clause
        ; body3 <- handleM 4 (underLet (bodyName p body,rng) frag2
                             (underLam frag99 (bodyName p body,rng)
                             (typeBody mod body (Check rng)))) err
        ; escapeCheck body t frag99
        ; return(loc,p1,body3,ds2) }

typeMatch mod (loc,p,body,ds) (Infer ref) = newLoc loc $
     do { (dom,frag1,p1) <- inferBndr localRename nullFrag p
        ; (frag2,ds2) <- underLam frag1 ("where ...",starR) (inferBndrForDecs localRename ds)
        ; (rng,body3) <- (underLet (bodyName p body,starR) frag2
                         (underLam frag1 (bodyName p body,starR)
                         (infer body)))
        -- ESCAPE CHECK
        ; escapeCheck body rng frag1
        ; writeRef ref (arrow dom rng)
        ; return(loc,p1,body3,ds2) }



instance Typable (Mtc Z TcEnv Pred) (Match Pat Exp Dec) Rho where
  tc = typeMatch Wob
----------------------------------------------------------------
-- The main workhorse which does Exp. This is modelled after the
-- function in "Practical type inference for arbitrary-rank types"
-- by Simon Peyton Jones and Mark Shields, modified to accomodate
-- "Simple Unification-based Type Inference for GADTS" by Simon
-- Peyton Jones, Stephanie Weirich, and Dimitrios Vytiniotis

instance Typable (Mtc Z TcEnv Pred) Exp Rho where
  tc = typeExp Wob

inferExp :: Exp -> TC(Rho,Exp)
inferExp = infer

typeExp :: Mod -> Exp -> Expected Rho -> TC Exp
typeExp mod (Lit x) expect = do { x' <- tc x expect; return (Lit x') }
typeExp mod (Var v) expectRho =
     do { m <- getLevel
        ; (sigma,mod,n,exp) <- lookupVar v
        ; when (n > m) (failD 2 [Ds (show v++" used at level "++show m++" but defined at level "++show n)])

        ; when (show v=="")
            (do { truths <- getTruths
                ; warn  [Ds ("\nChecking variable "++show v)
                        ,Ds "\nSigma = ",Dd sigma
                        ,Ds "\nExpect = ", Dd expectRho
                        ,Ds "\nTruths = ",Dl truths ", "]
                ; return ()})

        ; morePoly (Var v) sigma expectRho
        ; return exp }

typeExp mod e@(Sum inj x) (Check (Rsum t1 t2)) = -- t1 or t2 or both are non-trivial Sigmas
     do { (sig::Sigma,e) <- infer x
        ; case inj of { L -> morepoly (show e) sig t1
                      ; R -> morepoly (show e) sig t2 }
        ; return (Sum inj e) }
typeExp mod (Sum inj x) expect =
     do { (a,b) <- expecting "Sum" tsum expect
        ; e <- typeExp mod x (Check(case inj of { L -> a; R -> b }))
        ; return(Sum inj e) }

typeExp mod e@(Prod x y) (Check (Rpair t1 t2)) = -- t1 or t2 or both are non-trivial Sigmas
     do { (s1::Sigma,e1) <- infer x
        ; (s2::Sigma,e2) <- infer y
        ; morepoly (show e) s1 t1
        ; morepoly (show e) s2 t2
        ; return (Prod e1 e2) }
typeExp mod (Prod x y) expect =
     do { (a,b) <- expecting "Pair" tpair expect
        ; e1 <- typeExp mod x (Check a)
        ; e2 <- typeExp mod y (Check b)
        ; return (Prod e1 e2) }

typeExp mod (e@(App fun arg)) expect =
     do { (fun_ty,f) <- infer fun
        ; (arg_ty, res_ty) <- handleM 2 (unifyFun fun_ty) (notfun e fun_ty)
        ; x <- handleM 2 (check arg arg_ty) (badarg e arg_ty)
        ; zz <- zonk arg_ty
        ; ww <- zonk res_ty
        ; d <- getDisplay
        {-
        ; whenDd (show fun == "half") d
            [Ds ("\nChecking application: "++show e)
            ,Ds "\nfun type = ",Dd fun_ty
            ,Ds "\narg type = ",Dd zz
            ,Ds "\nresult type = ",Dd ww
            ,Ds "\n expected type = ",Dd expect]
        -}
        ; ns4 <- morePoly e res_ty expect
        ; return(App f x) }
typeExp mod (exp@(Lam ps e _)) (Check t) =
     do { (frag,ps2,result) <- checkBndrs localRename mod nullFrag ps t
        ; e2 <- underLam frag (show e,result) (typeExp mod e (Check result))
        ; escapeCheck exp t frag
        ; return(Lam ps2 e2 []) }
typeExp mod (exp@(Lam ps e _)) (Infer ref) =
     do { (ts2,frag,ps2) <- inferBndrs localRename nullFrag ps
        ; (t,e2) <-  underLam frag (show e,starR) (infer e)
        -- ESCAPE CHECK
        ; escapeCheck exp t frag
        ; writeRef ref (foldr arrow t ts2)
        ; return(Lam ps2 e2 []) }
typeExp mod term@(Ann body pt) exp_ty =
     do { (ann_ty,_) <- checkPT pt
        ; exp <- check body ann_ty
        ; morePoly term ann_ty exp_ty
        ; return (Ann exp pt) }
typeExp mod (Let ds e) expect =
     do { (frag,ds2) <- inferBndrForDecs localRename ds
        ; let pickRho (Check r) = r
              pickRho (Infer _) = starR
        ; e2 <- underLet (show e,pickRho expect) frag (typeExp mod e expect)
        ; return(Let ds2 e2)}
typeExp mod (Circ vs e ds) expect = tcCircuit vs e ds expect
typeExp mod (Case exp ms) (Check rng) =
     do { dom <- newTau star
        ; e2 <- typeExp Wob exp (Check(Rtau dom))
        ; (dom2,mod2) <- rigidity dom
        ; ms2 <- checkL (modAnd mod mod2) ms (Check (arrow (simpleSigma dom2) rng))
        ; return(Case e2 ms2) }
typeExp mod (Case exp ms) (Infer ref) =
     do { rng <- newRho star
        ; (dom,e2) <- infer exp
        ; ms2 <- checkL Wob ms (Check (arrow dom rng))
        ; writeRef ref rng
        ; return(Case e2 ms2) }
typeExp mod s@(Do ss) expect =
      do { (m,b) <- unifyMonad expect
         ; (bindSig,bmod,bn,bexp) <- lookupVar (Global "bind")
         ; (failSig,fmod,fn,fexp) <- lookupVar (Global "fail")
         ; bindt <- bindtype m
         ; failt <- failtype m
         ; morepoly "bind" bindSig bindt
         ; morepoly "fail" failSig failt
         ; ss2 <- tcStmts mod m b ss
         ; return(Do ss2)}
typeExp mod (CheckT e) expect =
     do { ts <- getBindings
        ; truths <- zonk ts
        ; assumptions <- getAssume
        ; ass2 <- mapM nf assumptions

        ; typ <- zonk expect
        ; d1 <- getDisplay
        ; d4 <- warnD d1 [Ds ("\n\n*** Checking: " ++ (take 62 (show e)))
                         ,Ds "\n*** expected type: ",Dd typ
                         ,Ds "\n***         Where: ",Dd truths
                         ,Ds "\n***        Truths: ",Dl assumptions ", "
                         ,Ds "\n***   norm Truths: ",Dl ass2 ", "]
        ; env <- tcEnv
        ; d5 <- checkLoop typ d4 env
        ; x <- setDisplay d5 (typeExp mod e expect)
        ; return(CheckT x)}
typeExp mod (Lazy e) expect = do { x <- typeExp mod e expect; return(Lazy x)}
typeExp mod (Exists e) (Check (Rtau (TyEx xs))) =
     do { (vs,preds,tau) <- instanL xs  -- ## WHAT DO WE DO WITH THE PREDS?
        ; typeExp mod e (Check (Rtau tau))}
typeExp mod (p@(Exists e)) expect =
    failD 2 [Ds "Existential expressions cannot have their type inferred:\n   ", Dd p
            ,Ds "\n   The type expected is:\n   ", Dd expect
            ,Ds "\n   which does not have form (exist s . type_exp)."
            ,Ds "\n   Probable fix: Remove the 'Ex' packing operator, or add 'exists' to the prototype."]
typeExp mod (Under e1 e2) expect = error "Under"
typeExp mod (Bracket exp) expect =
     do { a <- unifyCode expect
        ; e <- levelInc (typeExp mod exp (Check a))
        ; return(Bracket e)}
typeExp mod (Escape exp) expect =
     do { n <- getLevel
        ; case (n,expect) of
           (0,_) -> failD 2 [Ds ("Esc at level 0: "++show (Escape exp))]
           (_,Check t) ->
              do { e <- levelDec(typeExp mod exp (Check(tcode t)))
                 ; return(Escape e)}
           (_,Infer ref) ->
              do { t <- newRho star
                 ; e <- levelDec (typeExp mod exp (Check (tcode t)))
                 ; writeRef ref t
                 ; return(Escape e) }}
typeExp mod (Run exp) (Check t) =
      do { e <- typeExp mod exp (Check(tcode t)); return(Run e)}
typeExp mod (Run exp) (Infer ref) =
      do { t <- newRho star
         ; e <- typeExp mod exp (Check(tcode t))
         ; writeRef ref t
         ; return(Run e) }
typeExp mod (Reify s v) expect = error ("Unexpected reified value: "++s)


checkL mod [] expect = return []
checkL mod (t:ts) expect =
   do { t2 <- typeMatch mod t expect
      ; ts2 <- checkL mod ts expect
      ; return(t2:ts2) }




tcStmts mod m b [] = failD 2 [Ds "Do should have at least one statement"]
tcStmts mod m b [NoBindSt loc e] =
   do { e2 <- newLoc loc (typeExp mod e (Check (Rtau (TyApp m b))))
      ; return([NoBindSt loc e2])}
tcStmts mod m b [st@(BindSt loc pat e)] =
   failD 2 [Ds ("Last stmt in Do must not be a bind: "++show st)]
tcStmts mod m b [st@(LetSt loc ds)] =
   failD 2 [Ds("Last stmt in Do must not be Let: "++show st)]
tcStmts mod m b ((LetSt loc ds):ss) =
   do { (frag,ds2) <- inferBndrForDecs localRename ds
      ; ss2 <- underLet ("do { let ds; ... }",starR) frag (tcStmts mod m b ss)
      ; return((LetSt loc ds2):ss2)}
tcStmts mod m b ((NoBindSt loc e):ss) =
   do { a <- newTau star
      ; e2 <- typeExp Wob e (Check (Rtau(TyApp m a)))
      ; ss2 <- tcStmts mod m b ss
      ; return((NoBindSt loc e2):ss2)}
tcStmts mod m b ((BindSt loc pat e):ss) =
   do { a <- newTau star
      ; e2 <- typeExp Wob e (Check(Rtau(TyApp m a)))
      -- Smart scrutinee from "Simple Unification Based Type Inference for GADTS"
      ; (a2,mod2) <- rigidity a
      ; (frag,p2) <- checkBndr localRename mod nullFrag (simpleSigma a2) pat
      ; b2 <- applyTheta mod frag b
      ; ss2 <- underLam frag ("do { "++show pat++" <- e; ... }",starR)
                             (tcStmts (modAnd mod mod2) m b2 ss)
      ; return((BindSt loc p2 e2):ss2)}

rigidity t = do { t2 <- zonk t; return (t2,isRigid t2) }

modAnd Rig x = x
modAnd Wob _ = Wob

isRigidR (Rtau x) = isRigid x
isRigidR x = Wob

isRigid (TcTv(Tv _ (Rigid _ _ _) _)) = Rig
isRigid (TcTv(Tv _ _ _)) = Wob
isRigid (TyApp x y) = modAnd (isRigid x) (isRigid y)
isRigid (TyCon _ _ _) = Rig
isRigid (Star n) = Rig
isRigid (Karr x y) = modAnd (isRigid x) (isRigid y)
isRigid (TyVar _ _) = Rig
isRigid (TySyn _ _ _ _ x) = isRigid x
isRigid (TyEx zs) = case unsafeUnwind zs of
                     (vs,(ps,tau)) -> isRigid tau
isRigid (TyFun f xs k) = Wob





unifyMonad :: TyCh a => Expected Rho -> a (Tau,Tau)
unifyMonad (Check (Rtau (TyApp m a))) = return (m,a)
unifyMonad expected =
  do { a <- newTau star
     ; m <- newTau star_star
     ; zap (m,a) (Rtau (TyApp m a)) expected }


-----------------------------------------------------------------

t1 :: IO [()]
t1 = mapM (uncurry test) subpairs

test :: String -> String -> IO ()
test s1 s2 = runTC tcEnv0
  ((case (parsePT s1,parsePT s2) of
    (a@(Forallx All xs _ x),b@(Forallx All ys _ y)) ->
        do { (t1,_) <- checkPT a
           ; (t2,_) <- checkPT b
           ; b <- morepoly "test" t1 t2; outputString (show b ++ "\n") }
    (a@(Forallx All xs _ x),y) ->
        do { (t1,_) <- checkPT a
           ; t2 <- toRho typeConstrEnv0 y
           ; b <- morepoly "test"  t1 t2; outputString (show b ++ "\n") }
    (x,y) ->
        do { t1 <- toRho typeConstrEnv0 x
           ; t2 <- toRho typeConstrEnv0 y
           ; b <- morepoly "test"  t1 t2; outputString (show b ++ "\n") }) :: TC ())


----------------------------------------------------------------------------
-- when we have a [Dec] some of these Decs might be type signature like:
-- f :: a -> b -> M c
-- We want to take these and "push them down" onto the other Dec in the list.
-- This is done by placing them as annotations in Pat decls, and as optional
-- "hints" in Fun decls, data decls, and type-fun decls

pushHints [] d = d
pushHints protos (Fun loc nm _ ms) = Fun loc nm (applyName protos nm) ms
pushHints protos (Data loc b n nm sig vs cs ders) = Data loc b n nm (applyName protos nm) vs cs ders
pushHints protos (Val loc p body ds) = Val loc (applyPat protos p) body ds
pushHints protos (Reject s d) = Reject s d
pushHints protos (TypeFun loc nm sig ms) = TypeFun loc nm (applyName protos (Global nm)) ms
pushHints protos d = d

applyName [] nm = Nothing
applyName ((TypeSig loc var t):ps) nm =
  if nm==var then Just t else applyName ps nm

applyPat protos (pat@(Pvar var)) =
   case applyName protos var of
     Just t -> (Pann pat t)
     Nothing -> pat
applyPat protos (pat@(Paspat var p)) =
   case applyName protos var of
     Just t -> (Pann (applyPat protos p) t)
     Nothing -> pat
applyPat protos x = patg (applyPat protos) x

useTypeSig :: [Dec] -> [Dec]
useTypeSig decs = map (pushHints ps) ds
  where (ps,ds) = partition typeSigP decs
        typeSigP (TypeSig _ _ _) = True
        typeSigP _ = False

------------------------------------------------------

---------------------------------


frag0 = Frag (map f vals) [] [] [] [] []
  where f (nm,(v,sigma)) = (Global nm,(sigma,Rig,0,Var (Global nm)))

initTcEnv = addFrag frag0 tcEnv0


-- A version in the FIO monad that returns unresolved NEED as well
-- as the final TcEnv and the transformed Decs

checkDecs :: TcEnv -> [Dec] -> FIO Z (TcEnv,[Dec],[Pred])
checkDecs env ds = do { ((a,b),c) <- unTc (checkAndCatchGroundPred ds) env
                      ; return(b,a,c)}

-- when we check a declaration constraints that don't mention
-- any of the variables in the decl are passed upwards to be solved
-- by enclosing decls. At top level, their are no enclosing decls
-- and the only constraints that get passed upwards are ones with
-- no variables (we hope). Here is where we try and solve them.

checkAndCatchGroundPred ds =
  do { ((ds,env),ground::[Pred]) <- extractAccum(checkBndGroup ds)
     ; let message = "Solving toplevel ground terms"
     ; unsolved <- solveConstraints (message,starR) [] ground
     ; injectAccum unsolved
     ; return(ds,env)
     }





computeTheorems names env =  mapM f names
  where f (v@(Global nm)) =
          do { (sigma,mod,n,exp) <- lookupVar v
             ; sigmaToLemma nm sigma }

checkBndGroup :: [Dec] -> TC([Dec],TcEnv)
checkBndGroup [d@(AddTheorem xs)] =
  do { env <- tcEnv
     ; theorems <- computeTheorems xs env
     ; let env2 = env{rules = appendFMmany (rules env) theorems}
     ; return([d],env2)
     }
checkBndGroup [d@(TypeSyn loc nm args pt)] =
  do { env <- tcEnv
     ; (argBinds,rng) <- newLoc loc (useSigToKindArgs 0 args Nothing)
     ; (_,argsAsNames,argEnv) <- argsToEnv argBinds []
     ; (tau,monoKind,_) <- inferPT argEnv pt
     ; let g [] t = t
           g ((nm,k,q):ks) t = karr k (g ks t)
     ; polykind <- generalize(g argsAsNames monoKind)
     ; let f (nm,k,_) = (nm,k)
           ans = case length args of
                  0 -> TySyn nm 0 [] [] tau
                  n -> TySyn nm n (map f argsAsNames) [] tau
     ; return([d],env{type_env = (nm,ans,K polykind):(type_env env)})
     }
checkBndGroup ds | all isTypeFun ds =
  do { let ds2 = useTypeSig ds   -- push the signatures inside the TypeFun definitions
     ; env <- tcEnv
     ; env2 <- computeTypeFunEnv env ds2
     ; pairs <- hasMonoTypeypeFuns env2 ds2
     ; let env4 = env2{tyfuns = pairs ++ tyfuns env2}
     ; return(ds2,env4)}
checkBndGroup ds | all isData ds =
  do { (sigma,frag,ds2) <- checkDataDecs typeStrata  (useTypeSig ds) -- inferBndr False ds
     -- ; (preds,unifier) <- fragMGU ("Checking declaration group",starR) frag
     ; env <- (letExtend frag tcEnv)
     ; return(ds2,env)
     }
checkBndGroup ds | all isKind ds =
  do { (sigma,frag,ds2) <- checkDataDecs kindStrata  (useTypeSig ds) -- inferBndr False ds
     -- ; (preds,unifier) <- fragMGU ("Checking declaration group",starR) frag
     ; env <- letExtend frag tcEnv
     ; return(ds2,env)
     }
checkBndGroup ds =
  do { (frag,ds2) <- inferBndrForDecs False ds
    --  ; (preds,unifier) <- fragMGU ("Checking declaration group",starR) frag
     ; env <- letExtend frag tcEnv
     ; return(ds2,env)
     }


--------------------------------------------------------------------
-- Code for doing kind inference and evaluating type functions like
-- plus :: (Nat ~> Nat ~> Nat)
-- {plus (S x) y} = S {plus x y}
-- {plus Z y} = y

computeTypeFunEnv :: TcEnv -> [Dec] -> TC TcEnv
computeTypeFunEnv env xs =
  do { triples <- mapM f xs
     ; return (env{ type_env = triples ++ type_env env })}
 where f (t@(TypeFun loc nm Nothing ms)) =
         fail ("\nType functions must be explicitly kinded with kind signature\n"++show t)
       f (TypeFun loc nm (Just pt) ms) =
          do { (nmSigmaType,monoKind,nmTypeKind,names) <- inferPolyPT [] pt
             ; let poly = K(nmSigmaType)
             ; return (nm,TyCon (lv 1 {- TODO LEVEL -}) (nm) poly,poly) }

hasMonoTypeypeFuns :: TcEnv -> [Dec] -> TC [(String,[Tau] -> TC Tau,DefTree TcTv Tau)]
hasMonoTypeypeFuns env [] = return []
hasMonoTypeypeFuns env1 (dd@(TypeFun loc nm (Just pt) ms) : more) =
  do { (nmSigmaType,monoKind,nmTypeKind,names) <- inferPolyPT [] pt
     ; let polyt@(K(sigma)) = K(nmSigmaType)
     ; clauses <- mapM (checkLhsMatch (type_env env1) sigma) ms
     ; let f d (ts,ps,t) = displays d [Dl ts ",",Ds " ----> ",Dd t]
     ; morepairs <- hasMonoTypeypeFuns env1 more
     ; rule <- makeRule nm polyt clauses
     ; tree <- case defTree rule of
                 (t:ts) -> return t
                 [] -> failD 0 [Ds ("\nThe type function "++nm++" is not inductively sequential.\n")
                               ,Ds (show dd)]
     ; return ((nm,undefined {- makeTfun nm poly clauses -},tree): morepairs)
     }

makeRule s k xs =
  do { let f (lhsexps,lhspats,rhs) =
              do { let (_,vs) = varsOfTau (TyFun s k (rhs:lhsexps))
                       new (nm,kind) = newFlexiTyVar kind
                       pick (nm,kind) var = (nm,TcTv var)
                 ; us <- mapM new vs
                 ; let env = (zipWith pick vs us,[],[],[]) -- TODO LEVEL
                 ; newlhs <- mapM (sub env) lhsexps
                 ; newrhs <- sub env rhs
                 ; return (us,newlhs,newrhs)}
     ; zs <- mapM f xs
     ; return(NarR(NTyCon s k,zs)) }

-- Successful kind-checking of a type function returns a [([Tpat],Tau)]
-- from this we must produce a function with type: [Tau] -> TC Tau. We do
-- this using two functions tmatch and teval

makeTfun :: String -> PolyKind -> [([Tau],[Tpat],Tau)] -> ([Tau] -> TC Tau)
makeTfun s k [] = return . TyFun s k
makeTfun s k ((lhs,ps,body):more) = f
  where f args = case matchmany ps args [] of
                   Just env ->  error "Call to teval" -- teval env body
                   Nothing -> makeTfun s k more args


matchmany [] [] env = return env
matchmany (p:ps) (t:ts) e0 = do { e1 <- tmatch p t e0; matchmany ps ts e1 }
matchmany _ _ _ = Nothing

tmatch:: Tpat -> Tau -> [(Name,Tau)] -> Maybe [(Name,Tau)]
tmatch (Tvar s nm) t env =
   case lookup nm env of
     Nothing -> Just((nm,t):env)
     Just t2 -> if t==t2 then Just env else Nothing
tmatch (Tstar n) (Star m) env = if n==m then Just env else Nothing
tmatch (Tkarr x y) (Karr a b) env = do { e1 <- tmatch x a env; tmatch y b e1}
tmatch (Tcon s []) (TyCon level_ t k) env = if s==t then Just env else Nothing
tmatch (Tcon s ps) (app@(TyApp _ _)) env =
  do { let down (TyApp (TyCon level_ s k) x) = return(s,[x])
           down (TyApp x y) = do { (c,ys) <- down x; return(c,ys++[y])}
           down y = Nothing
     ; (g,ys) <- down app
     ; if g==s then matchmany ps ys env else Nothing}
tmatch (Tfun s ps) (TyFun t _ xs) env | s==t = matchmany ps xs env
tmatch x (TySyn nm n fs as y) env = tmatch x y env
tmatch (Tapp x y) (TyApp a b) env = do { e1 <- tmatch x a env; tmatch y b e1}
tmatch x (TyEx xs) env = error "No matching for existentials yet"
tmatch x y env = Nothing


-- check the lhs (i.e. {plus (S x) y} = ... ) of each match

checkLhsMatch :: ToEnv -> Sigma -> ([PT],PT) -> TC ([Tau],[Tpat],Tau)
checkLhsMatch current sigma (ps,rhs) =
  do { -- Fresh Instance of the type for every clause
       (vars,_,Rtau tau) <- unBindWith newflexi sigma
     ; let down (Karr x y) xs = down y (xs++[x])
           down rng xs = (rng,xs)
           (range,ks) = down tau []
     ; (_,pats) <- thrd [] pTtoTpat (tail ps)   -- ps = {plus (S x) y} throw away "plus"
     ; when (not(length ks == length pats))
            (failD 3 [Ds "\nThe number of arguments in the function call: "
                     ,Dd (TyFun' ps)
                     ,Ds "\ndoes not match type signature: "
                     ,Dd (foldr Karr range ks)])
     ; envs <- mapM (checkPTBndr current) (zip pats ks)
     ; let rhsFree = getFree [] rhs
           lhsFree = map (\ (nm,tau,kind) -> nm) (concat envs)
           f s = do { m <- newTau (MK (Star 2))
                    ; k <- newTau (MK m)
                    ; nm <- fresh; return (s,TyVar nm (MK k),poly (MK k))}
     ; additional <- mapM f (rhsFree \\ lhsFree)
     -- ; when (not (null additional)) (outputString ("Additional = "++show additional))
     ; let newenv = concat envs ++ current
     ; lhsTau <- mapM (toTau newenv) (tail ps)
     ; lhsExps <- mapM (uncurry check) (zip lhsTau ks)
     ; rhsTau <- toTau (additional ++ newenv) rhs
     ; w <- check rhsTau range
     ; return(lhsExps,pats,w)
     }

-- In order to faciliate evaluation, we define a new data type that
-- encodes patterns that match Tau-type expressions

data Tpat
  = Tvar String Name
  | Tcon String [ Tpat ]
  | Tstar Int
  | Tkarr Tpat Tpat
  | Tfun String [ Tpat ]
  | Tapp Tpat Tpat

instance Show Tpat where
  show x = y where (disp2,y) = exhibit () x

instance NameStore d => Exhibit d Name where
  exhibit d1 nm = useStoreName nm star f d1 where f s = "'"++s

instance NameStore d => Exhibit d Tpat where
  exhibit d1 (Tvar s nm) = useStoreName nm star f d1
    where f s = "'"++s
  exhibit d1 (Tcon s []) = (d1,s)
  exhibit d1 (Tcon s xs) = (d2,"(" ++ s ++" "++zs++")")
    where (d2,zs) = exhibitL exhibit d1 xs " "
  exhibit d1 (Tfun s xs) = (d2,"{" ++ s ++" "++zs++"}")
    where (d2,zs) = exhibitL exhibit d1 xs " "
  exhibit d1 (Tstar n) = (d1,"*"++show n)
  exhibit d1 (Tkarr a b) = (d2,"("++x++" ~> "++y++")")
    where (d2,x,y)= exhibit2 d1 (a,b)
  exhibit d1 (Tapp a (b@(Tapp _ _))) = (d2,x++ " ("++y++")")
    where (d2,x,y) = exhibit2 d1 (a,b)
  exhibit d1 (Tapp a b) = (d2,x++" "++y)
    where (d2,x,y) = exhibit2 d1 (a,b)

instance (NameStore d,Exhibit d x) => Exhibit d (Body x) where
  exhibit d (Normal e) = exhibit d e
  exhibit d (Guarded xs) = (d,"NoGuards yet")

-----------------------------------------------------------------------
-- Translate a PT (the type that is parsed) into a Tpat. This is relatively
-- straightforward, the only difficult part is that every type application
-- must start with a TyCon, or it won't be a legitimate type-pattern
-- and that duplicate names (i.e. a var that appears twice in a pattern)
-- must map to the same Tvar for every occurrence.

pTtoTpat :: HasNext m => PT -> [(String,Tpat)] -> m ([(String,Tpat)],Tpat)
pTtoTpat (TyVar' s) env =
  case lookup s env of
    Nothing -> do { nm <- fresh; let u = Tvar s nm in return((s,u):env,u)}
    Just v -> return(env,v)
pTtoTpat (x@(TyApp' _ _)) e1 =
  do { let down (TyApp' (TyCon' s) x) = return(s,[x])
           down (TyApp' x y) = do { (c,ys) <- down x; return(c,ys++[y])}
           down y = fail ("Root of ("++show x++") is not a type constructor: "++show y)
     ; (constr,args) <- down x
     ; (e2,params) <- thrd e1 pTtoTpat args
     ; return(e2,Tcon constr params)}
pTtoTpat (Rarrow' x y) e1 =
  do { (e2,dom) <- pTtoTpat x e1
     ; (e3,rng) <- pTtoTpat y e2
     ; return(e3,Tcon "(->)" [dom,rng])}
pTtoTpat (Karrow' x y) e1 =
  do { (e2,dom) <- pTtoTpat x e1
     ; (e3,rng) <- pTtoTpat y e2
     ; return(e3,Tkarr dom rng)}
pTtoTpat (TyCon' s) e1 = return(e1,Tcon s [])
pTtoTpat (Star' n) e1 = return(e1,Tstar n)
pTtoTpat (TyFun' (TyVar' s : xs)) e1 =
  do { (e2,ys) <- thrd e1 pTtoTpat xs
     ; return(e2,Tfun s ys) }
pTtoTpat x e1 = fail ("The type: "++show x++" is not appropriate for the LHS of a type fun.")

----------------------------------------------------------------------
-- This code is used to translate a sigma type into a rule.
-- given (forall a . P a => T a -> S a -> Q a)
-- We need to test that T,S, and Q are all Proposition constructors.
-- The rule would be  Q a -> T a, S a  When P a
-- we need to translate (Q a) into a pattern so that we can
-- match Propositions against it to obtain a binding for "a"
-- Rules are classifed as Axiom or Theorem depending upon if
-- the function is the type of a Constructor function (Axiom) of a
-- prop or if it is the type of a total function (Theorem).

data RuleClass = Axiom | Theorem | Lemma deriving Show


--               name   key    class     Vars                Precond Lhs  Rhs
data RWrule = RW String String RuleClass [(Name,Kind,Quant)] [Pred]  Pred [Pred]
--                                       Quant=Ex if Name not in LHS

rname (RW nm key rclass args precond lhs rhs) = nm
rkey  (RW nm key rclass args precond lhs rhs) = key

----------------------------------------------------------------------------
-- Solving a list of predicates returns a second list of, hopefully,
-- simpler predicates. If the returned list is empty, then the input
-- is solved.

solveConstraints (context,rho) truths [] = return []
solveConstraints (context,rho) truths cs =
  do { let (ps,eqs,un0) = split3 cs
     -- ; warn [Ds ("\nSolving constraints in context "++context)
     --       ,Ds "\nTruths = ",Dl truths ","
     --       ,Ds "\ncontraints = ",Dl cs ","]
     ; (ps2,eqs2) <- sub ([],un0,[],[]) (ps,eqs) -- TODO LEVEL
     ; un1 <- solveByNarrowing (3,25) ("1. "++context,rho) truths eqs2
     ; un2 <- mutVarSolve un1
     ; ps3 <- sub ([],un2,[],[]) ps2 -- TODO LEVEL
     ; truths2 <- expandTruths truths
     --; warn [Ds "Just before solvP, truths = ",Dl truths ","
     --       ,Ds "; and need = ",Dl ps3 ","]
     ; (ps4,un3) <- solvP truths2 ps3
     ; mutVarSolve un3
     ; zonk ps4
     }


data Result = Rs (DispInfo Z) [(TcTv,Tau)] [Pred]

solvePred :: DispInfo Z -> Bool -> [Pred] -> [Pred] -> TC Result
solvePred d0 verbose truths [] = return (Rs d0 [] [])
solvePred d0 verbose truths ((r@(Rel term)):morepreds) =
  if elem r truths
     then solvePred d0 verbose truths morepreds
     else do { t <- zonk term
             ; s <- predNameFromTau term t
             ; rules <- getMatchingRules s
             ; d1 <- report3 d0 verbose t truths rules
             ; (Rs d2 u1 xs) <- solveButReturnInputIfFail verbose d1 truths rules (Rel t)
             ; (Rs d3 u2 ys) <- solvePred d2 verbose truths morepreds
             ; xs2 <- removeAlreadyTrue truths xs
             ; return(Rs d3 (u1++u2) (xs2++ys))}
solvePred d0 verbose truths (p:ps) = failD 1 [Ds "unknown predicate: ", Dd p]

report3 d False t truths rules = return d
report3 d True t truths rules =
    warnD d  [Ds "\n-------------------\nSolving predicate: ",Dd t
             ,Ds "\n Truths = ",Dl truths ", "
             ,Ds "\n Rules = ",Dl (map rname rules) ","]


solveButReturnInputIfFail verbose d1 truths rules t =
  do { zs <- useManyRule verbose d1 truths rules t
     ; case zs of
         Just (Rs d2 u residual) -> return (Rs d2 u residual)
         Nothing -> return (Rs d1 [] [t])
     }

report4 d False choices = return d
report4 d True  choices = warnD d [Ds " Choices = ",Dlf f choices ","]
  where f d (r,args,unifier,pre,results) = (d,rname r)

useManyRule :: Bool -> DispInfo Z -> [Pred] -> [RWrule] -> Pred -> TC (Maybe Result)
useManyRule verbose d1 truths rules (Equality x y) = (solveEqAssump d1 x y)
useManyRule verbose d1 truths rules (EqAssump x y) = (solveEqual d1 x y)
useManyRule verbose d1 truths [] t = return Nothing
useManyRule verbose d1 truths rules (p@(Rel term)) =
  do { choices <- possibleMatches rules term
     ; tryToRefute rules term
     ; d2 <- report4 d1 verbose choices
     ; solveOneOf verbose d2 truths choices p
     }


-- A goal is refuted if it doesn't unifies with the lhs of any Axiom

tryToRefute rules term =
  ifM (refute rules term)
      (failD 3 [Ds "The proposition: (",Dd term,Ds ") can never be solved."])
      (return ())

refute [] term = return True
refute ((r@(RW nm key Lemma _ _ _ _)):rs) term = refute rs term
refute ((r@(RW nm key Theorem _ _ _ _)):rs) term = refute rs term
refute ((r@(RW nm key Axiom   _ _ _ _)):rs) term =
  do { (Rel lhs) <- freshLhs r
     ; case mgu [(lhs,term)] of
        Left sub -> return False
        Right _ -> refute rs term
     }

refutable :: [Pred] -> TC (DispElem Z)
refutable [] = return (Ds "")
refutable ((Rel term):ps) =
  do { t <- zonk term
     ; s <- predNameFromTau term t
     ; rules <- getMatchingRules s
     ; ifM (refute rules t)
           (return(Dr [Ds "The proposition: (",Dd t,Ds ") is refutable."]))
           (refutable ps) }
refutable (p:ps) = refutable ps


solveOneOf :: Bool -> DispInfo Z -> [Pred] ->
              [RuleMatch] ->
              Pred ->
              TC (Maybe Result)
solveOneOf verbose d1 truths [] p = return Nothing
solveOneOf verbose d1 truths ((r,args,unifier,pre,results):morechoices) p =
   do { d2 <- report1 verbose d1 r unifier pre results
      ; let try [] = solveOneOf verbose d2 truths morechoices p
            try ((u,preconditions):moreMatches) =
                do { d3 <- report2 verbose d2 u
                   ; ifM (discharge (subPred u truths) preconditions)
                         (return(Just(Rs d3 u (subPred u results))))
                         (try moreMatches)}
      ; try (truthConsistentPreConds args truths pre unifier)
      }

discharge :: [Pred] -> [Pred] -> TC Bool
discharge truths obligations = handleM 9 try fail
  where try = do { (Rs d u residual) <- solvePred disp0 False truths obligations
                 ; return(null residual)}
        fail _ _ = return False


report1 False d1 r unifier pre results = return d1
report1 True  d1 r unifier pre results =
  warnD d1 [Ds "\ntrying ",Dd r,Ds "\nUnifier = ",Dl unifier ", "
           ,Ds "\nPreconditions = ", Dl pre ", "
           ,Ds "\nResults = ",Dl results ", "]

report2 False d2 u = return d2
report2 True  d2 u = warnD d2 [Ds "\nExtended = ",Dd u]


------------------------------------------------------------------------
-- If a rule has existentially quantified variables, Like the
-- "b" in   Le a b -> Le b c -> Le a c    which in rule form would be
--  [Le a b,Le b c]: Le a c -> []         we need to handle this.
-- After matching a goal agiant (Le a c), we need to look in
-- the truths to see if there are instances of (Le a b) and (Le b c)
-- finding consistent bindings for "b", which successfully extend the bindings
-- obtained by matching the goal and (Le a c). If there are no existential bindings
-- it's not necessary to find any matches, just apply the bindings to the
-- preconditions and then solve them, perhaps by backchaining. This is
-- a rather weak method, but it will have to do for now.
-- If there are existential bindings then there may be multiple consistent
-- extensions, and we'll have to try all of them.


truthConsistentPreConds :: [(TcTv,Quant)] ->        -- vars to match on
                           [Pred] ->                -- truths
                           [Pred] ->                -- pre conditions
                           [(TcTv,Tau)] ->          -- bindings
                           [([(TcTv,Tau)],[Pred])]  -- a list of consistent answers

truthConsistentPreConds [] truths preconds unifier = [freshC2 preconds unifier]
truthConsistentPreConds vars truths preconds unifier = map (freshC2 preconds) goodU
  where possibleU = findInstances truths preconds unifier
        goodU = filter (\ u -> covers2 u vars) possibleU

freshC2 :: [Pred] -> [(TcTv,Tau)] -> ([(TcTv,Tau)],[Pred])
freshC2 conds u = (u,subPred u conds)

-------------------------------------------------------------------
-- Does a unifier provide a mapping for every variable
-- in the list of variables (that are existentially qualified)
-- i.e. those that do not appear in the range (those whose
-- Quant is Ex). For example: "b" in   Le a b -> Le b c -> Le a c

covers2 :: [(TcTv,Tau)] -> [(TcTv,Quant)] -> Bool
covers2 unifier [] = True
covers2 unifier ((v,All):xs) = covers2 unifier xs
covers2 unifier ((m,Ex):xs) =
  case lookup m unifier of
    Just t -> covers2 unifier xs
    Nothing -> False

----------------------------------------------------------------------
-- Given a rule (name: [pre1, ... ,preN]: lhs -> [rhs1, ... rhs2])
-- where lhs has already matched against a goal returning "bindings",
-- and where pre_i might contain existential vars, find a list of
-- consistent extentions to "bindings" where each of the pre_i match
-- some term in the set of truths.

findInstances :: [Pred] -> [Pred] -> [(TcTv,Tau)] -> [[(TcTv,Tau)]]
findInstances truths [] bindings = [bindings]
findInstances truths (Rel cond1:preconds) bindings = concat uss
  where us = unifiers bindings truths cond1
        recCall u = findInstances (subPred u truths) (subPred u preconds) u
        uss = map recCall us
        -- Note if "us" is [], there is no match (in truths) for at
        -- least one of the preconditions, so the whole result is [].
        -- For every unifier in "us", apply it to what's left of
        -- preconds, and the whole truths list, then recursive call
        -- on the transformed, smaller, list of preconditions.


-- return an extension of "unifier" for each time "pat"
-- matches an element of "truths"

unifiers :: [(TcTv,Tau)] -> [Pred] -> Tau -> [[(TcTv,Tau)]]
unifiers u [] pat = []
unifiers u ((Equality _ _):truths) pat = unifiers u truths pat
unifiers u ((EqAssump _ _):truths) pat = unifiers u truths pat
unifiers unifier ((Rel t):truths) pat =
  let rest = unifiers unifier truths pat
  in case mguBias [(pat,t)] of
      Left u -> case compose (Left u) (Left unifier) of
                 Left r -> r:rest
                 Right _ -> rest
      Right _ -> rest

------------------------------------------------------------------
-- Given a predicate and a set of rules, find and return a list
-- of possible matches. Each match is a fresh instance of a rule
-- with the binding variables freshly replaced.

type RuleMatch = (RWrule,[(TcTv,Quant)],[(TcTv,Tau)],[Pred],[Pred])

instance Exhibit (DispInfo Z) RuleMatch where
  exhibit d ((RW name key rclass _ _ _ _),vars,unifier,pre,result) =
    displays d [Ds ("\n"++show rclass++" "++name++" ")
               ,Dlf f vars ", ",Ds "\n Precondition = ",Dd pre
               ,Ds "\n results = ",Dd result
               ,Ds "\nUnifier = ", Dd unifier]
       where f d (v,q) = displays d [Dd v,Ds (":"++show q)]

-- ========================================================
-----------------------------------------------------------
-- We use Lemmas to try and establish narrowing equalities
-- that have ambiguous solutions. I.E we are left with
-- (Equality x y). We apply lemmas to rewrite both x and y
-- and then compare for equality. A lemma looks like
-- [Pred] => lhs -> rhs, A Pred is either (Equality a b)
-- or (Nat' x) for Now.  We establish (Equality a b) by
-- recursively using lemmas. (Nat' x) establishes for free.

comp new old =
  case compose (Left new) (Left old) of
    Left u3 -> return u3
    Right _ -> fail "compose fails"


rewrite:: [Tau] -> TC ([Tau],Unifier)
rewrite [] = return([],[])
rewrite (t:ts) =
  do { (t',u2) <- rew t
     ; (ts',u3) <- rewrite (map (subTau u2) ts)
     ; u4 <- comp u3 u2
     ; return(t':ts',u4)}

rew :: Tau -> TC(Tau,Unifier)
rew (TyVar nm k) = return(TyVar nm k,[])
rew (TyApp x y) =
   do { ([a,b],u) <- rewrite [x,y]; return(TyApp a b,u)}
rew (TyCon l nm k) = return(TyCon l nm k,[])
rew (Star n) = return(Star n,[])
rew (Karr x y) =
   do { ([a,b],u) <- rewrite [x,y]; return(Karr a b,u)}
rew (TyFun nm k xs) =
   do { (ys,unifier) <- rewrite xs
      ; let new = (TyFun nm k ys)
      ; rs <- getLemmaRules nm
      ; maybeM (applyLemmas rs new)
               return -- ( \ (newer,u2) -> return(newer,u2))
               (return(new,unifier)) }
rew (TcTv v) = return(TcTv v,[])
rew (TySyn nm n vs xs t) =
   do { (t':xs',u) <- rewrite (t:xs); return(TySyn nm n vs xs' t',u)}
rew (TyEx l) =
   do { (vs,(ps,body)) <- unwind l
      ; (body',u) <- rew body
      ; return(TyEx(windup vs (ps,body')),u)}

getLemmaRules nm =
  do { rules <- getMatchingRules nm
     ; let fresh x = do { info <- freshLemma x; return(x,info)}
     ; rs <- mapM fresh rules
     ; return rs}

tryRewriting t =
  do { (t2,u) <- rew t
     ; if t==t2
          then return Nothing
          else return (Just (t2,u))};

rewEq :: (Tau,Tau) -> TC(Maybe Unifier)
rewEq (t1 @(TyFun nm k xs),t2) =
          do {rs <- getLemmaRules nm; try True (t1,t2) rs}
  where try True (t1,t2@(TyFun nm k xs)) [] =
          do { rs <- getLemmaRules nm; try False (t2,t1) rs }
        try other (t1,t2) [] = return Nothing
        try other (t1,t2) ((lemma,(vs,[],lhs,rhs)):more) =
          case match [] [(lhs,t1),(rhs,t2)] of
            Just u -> do { warn [Ds ("\n*** Trying equality lemma '"++rname lemma)
                                ,Ds "' on term:\n   ",Dd (eqf t1 t2)]
                         ; return (Just [])} -- matching means no variables escape
            Nothing -> try other (t1,t2) more
        try other (t1,t2) (m:more) = try other (t1,t2) more
rewEq (_,_) = return Nothing

applyLemmas [] term = return Nothing
applyLemmas ((lemma,(vs,preds,lhs,rhs)):more) term =
  case match [] [(lhs,term)] of
    Just u1 -> do { let new = subN u1 rhs
                        preconds = (subPred u1 preds)
                  ; warn [Ds ("\n**Trying lemma '"++rname lemma++"' on term:\n   "),Dd term]
                  ; maybeM (establish preconds)
                           (\ u2 -> do { u3 <- comp u2 u1; return (Just (new,u3))})
                           (applyLemmas more term)}
    Nothing -> applyLemmas more term

useLemma :: Pred -> TC (Maybe [(TcTv,Tau)])
useLemma (Rel (TyApp (TyCon _ "Nat'" k) x)) = return(Just [])
useLemma (p@(Equality x y)) =
  do { ([x2,y2],s3) <- rewrite [x,y]
     ; if x2 == y2
          then return (Just s3)
          else return Nothing
     }
useLemma _ = return Nothing


establish :: [Pred] -> TC(Maybe [(TcTv,Tau)])
establish [] = return(Just [])
establish (p:ps) =
  maybeM (useLemma p)
         (\ u1 -> maybeM (establish ps)
                         (\ u2 -> do { u3 <- comp u2 u1; return (Just u3)})
                         (return Nothing))
         (return Nothing)

freshLemma :: RWrule -> TC ([(TcTv,Quant)],[Pred],Tau,Tau)
freshLemma r =
 do { info <- freshRule newflexi r
    ; case info of
       (vars,precond,Rel lhs,[Rel rhs]) -> return(vars,precond,lhs,rhs)
       _ -> failD 2 [Ds "In freshLemma ",Dd r,Ds " is not a lemma."]
    }

-- ========================================================
--------------------------------------------------------------------------
getMatches :: [RWrule] -> Tau -> TC[RuleMatch]
getMatches [] term = return []
getMatches ((r@(RW nm key Lemma _ _ _ _)):rs) term = getMatches rs term
getMatches ((r@(RW nm key rclass _ _ _ _)):rs) term =
  do { (vars,precond,Rel lhs,rhs) <- freshRule newSkolem r
     ; ys <- getMatches rs term
     ; case mguBias [(lhs,term)] of
        Left sub -> let pre2 = subPred sub precond
                        rhs2 = subPred sub rhs
                        r2 = RW nm key rclass (map pair2Triple vars) precond (Rel lhs) rhs
                    in return((r2,vars,sub,pre2,rhs2):ys)
        Right _ -> return ys
     }

-- when we match a rule:   pre => lhs -> rhs  against a "goal"
-- "lhs" will contain Skol vars, and "goal" might contain Flexi vars.
-- We match with mguBias [(lhs,goal)]  and we build a subsitution
-- from only the Skol vars in "lhs", and the Flexi vars in "goal",
-- The matching process is biased against all other vars matching
-- and prefers a Skol match over a Flexi match
-- Now a match that binds a Flexi var is only good if comes from an
-- Axiom, and that Axiom is the only match possible. If the goal can
-- never match any other Axiom, it is safe to bind the Flexi var when
-- we are done slving the contraints (but not before since the solving
-- may fail, and we don't want to commit that binding). So we filter
-- out matches that bind Flexi vars, if there is more than one match.

possibleMatches :: [RWrule] -> Tau -> TC[RuleMatch]
possibleMatches rules term =
   do { matches <- getMatches rules term
      ; case matches of
         [((RW n k Axiom a ps l r),_,_,_,_)] -> return matches
         other -> return(filter closedChoice matches)}
  where closedChoice (rule,_,bindings,_,_) = sideEffectFree bindings
        sideEffectFree :: [(TcTv,Tau)] -> Bool
        sideEffectFree [] = True
        sideEffectFree (((Tv unq (Flexi _) k),tau):more) = False
        sideEffectFree ((x,TcTv (Tv unq f k)):more) = sideEffectFree more
        sideEffectFree (m:more) = sideEffectFree more


pair2Triple :: (TcTv,Quant) -> (Name,Kind,Quant)
pair2Triple (Tv n _ k,q) = (integer2Name n,k,q)



freshRule :: (Name -> Quant -> Kind -> TC Tau) -> RWrule ->  TC ([(TcTv,Quant)],[Pred],Pred,[Pred])
freshRule new (RW nm key rclass args precond lhs rhs) =
    do { (env,pairs) <- buildEnv new args [] []
       ; precond2 <- subst env precond
       ; lhs2 <- subst env lhs
       ; rhs2 <- subst env rhs
       ; return(pairs,precond2,lhs2,rhs2)}

freshLhs :: RWrule -> TC Pred
freshLhs (RW nm key rclass args precond lhs rhs) =
    do { (env,pairs) <- buildEnv newflexi args [] []
       ; subst env lhs
       }

buildEnv newf [] env pairs = return (env,pairs)
buildEnv newf ((nm,k,q):xs) env pairs =
         do { k2 <- subst env k
            ; (var@(TcTv v)) <- newf nm q k2
            ; buildEnv newf xs ((nm,var):env) ((v,q):pairs) }



------------------------------------------------------------------------

checkRange sig (_:_) rng =
    failD 2 [Ds "Theorems cannot have constrained types yet: ",Dd sig]
checkRange sig [] rng =
 case rng of
   (TyApp (TyApp (con@(TyCon _ "Equal" k)) x) y) ->
      case (x,rootT x []) of
        (TyFun f _ _, any) -> return(con,f,x,y)
        (any,Just(f,k,zs)) -> return(con,f,x,y)
        other -> failD 2 [Ds "Only (Equal lhs rhs) theorems for now: ",Dd rng]
   _ -> failD 2 [Ds "Only (Equal lhs rhs) theorems for now: ",Dd rng]


sigmaToLemma :: String -> Sigma -> TC(String,RWrule)
sigmaToLemma name sigma =
 do { x <- instanTy sigma           -- The instanTy, generalize sequence
    ; (Forall xs) <- generalize x   -- removes Equality predicates
    ; (args,(conds,rho)) <- unwind xs
    ; warn [Ds "\n*** Adding Lemma: ",Dd rho]
    ; (doms,rng) <- case (getDomsRng rho) of
                     (Just p) -> return p
                     Nothing -> failD 2 [Ds "A non Tau type cannot be a rule: ",Dd sigma]
    ; (eqCon,key,x,y) <- checkRange sigma conds rng
    ; return(key,RW name key Lemma args (map Rel doms) (Rel x) [(Rel y)])
    }

{-
lemmaToTruths:: RWrule -> [Pred]
lemmaToTruth (rule@(RW name key Lemma args precond (Rel x) [(Rel y)]))
lemmaToTruth rule = []
-}

sigmaToRWrule :: RuleClass -> String -> Sigma -> TC RWrule
sigmaToRWrule rclass name (sigma@(Forall ss)) =
  do { x <- instanTy sigma           -- The instanTy, generalize sequence
     ; (Forall xs) <- generalize x   -- removes Equality predicates
     ; (args,(conds,rho)) <- unwind xs
     ; (doms,rng) <- case (getDomsRng rho) of
                      (Just p) -> return p
                      Nothing -> failD 2 [Ds "A non Tau type cannot be a rule: ",Dd sigma]
     ; key <- predNameFromTau rng rng
     ; let (_,bound) = varsOfTau rng
           (_,fr) = varsOfPred (map Rel doms ++ conds)
           eq (nm1,k1) (nm2,k2) = nm1==nm2
           free = deleteFirstsBy eq fr bound
           g (nm,k,q) = if any (eq (nm,k)) free then (nm,k,Ex) else (nm,k,All)
           args2 = map g args
           lhs = Rel rng
           rhs = if (null free) then (map Rel doms) else []
           preCond = conds ++ (if (null free) then [] else (map Rel doms))
           ans = (RW name key rclass args2 preCond lhs rhs)
     -- ; showD [Ds "Args = ",Dl args2 ", ",Ds "\n   ", Dd ans]
     ; return ans
     }


instance TypeLike (Mtc Z TcEnv Pred) RWrule where
  sub env (RW name key rclass args preCond lhs rhs) =
     do { (args2,env2) <- g args env; pre2 <- sub env2 preCond
        ; l2 <- sub env2 lhs; r2 <- sub env2 rhs
        ; return(RW name key rclass args2 pre2 l2 r2)}
    where g [] env = return ([],env)                -- args are binding occurrences
          g ((nm,k,q):xs) (env@(ns,vs,ss,level_)) = -- so extend the Name env so they
            do { k2 <- sub env k                    -- don't get inadvertantly substituted
               ; let env2 = ((nm,TyVar nm k2):ns,vs,ss,level_)
               ; (ys,envN) <- g xs env2
               ; return((nm,k2,q):ys,envN)}
  zonk (RW name key rclass args preCond lhs rhs)=
    do { let f (nm,k,q) = do { k2 <- zonk k; return(nm,k2,q)}
       ; a2 <- mapM f args; p2 <- zonk preCond
       ; l2 <- zonk lhs; r2 <- zonk rhs
       ; return(RW name key rclass a2 p2 l2 r2)}
  get_tvs f = error "No way to get the type vars from a RWrule"
  nf x = error "Can't put RWrules in normal form"



data PatPred = PP String Tpat Pred
pred2PP (r@(Rel t)) = do { s <- predNameFromTau t t; p <- tau2Tpat t; return(PP s p r)}

tau2Tpat :: TyCh m => Tau -> m Tpat
tau2Tpat (TyVar nm k) = return(Tvar (show nm) nm)
tau2Tpat (TyApp x y) =
  do { dom <- tau2Tpat x
     ; rng <- tau2Tpat y
     ; return(Tapp dom rng)}
tau2Tpat (TyCon l s k) = return(Tcon s [])
tau2Tpat (Star n) = return(Tstar n)
tau2Tpat (Karr x y) =
  do { dom <- tau2Tpat x
     ; rng <- tau2Tpat y
     ; return(Tkarr dom rng)}
tau2Tpat (TySyn s n fs as x) = tau2Tpat x
tau2Tpat (TyFun s k xs) =
  do { ys <- mapM tau2Tpat xs
     ; return(Tfun s ys) }
tau2Tpat x = failD 0 [Ds "The type: ",Dd x,Ds " is not appropriate for a proposition."]


splitIntoPredsRho s =
  do { x <- instanTy s                   -- The instanTy, generalize sequence
     ; sig@(Forall y) <- generalize x    -- removes Equality predicates
     ; (_,rho) <- instanTy sig
     ; (_,z) <- unwind y
     ; return (z,rho)
     };

isRuleCon :: String -> TC Bool -- Is the name of a TyCon
isRule "Equal" = return(True)  -- the name of a Proposition?
isRuleCon s =
 do { env <- tcEnv;
    ; return(Map.member s (rules env))
    }

predNameFromTau s (TyApp f y) = predNameFromTau s f
predNameFromTau s (TyCon l nm k) = return nm
predNameFromTau s x = failD 2 [Ds "\nNon Type constructor: "
                       ,Dd x
                       ,Ds " used as Prop in:\n  "
                       ,Dd s]

isPropM :: Rho -> [String] -> Tau -> TC Pred
isPropM sigma new t =
  do { s <- predNameFromTau sigma t;
     ; if elem s new
          then return (Rel t)
          else ifM (isRuleCon s)
                   (return (Rel t))
                   (failD 2 [Ds "\nThe type: ("
                            ,Dd t
                            ,Ds ") is not a proposition."
                            ])}

------------------------------------------------------------------
-- This code tests the type of a function to see if it could
-- be a theorem. It can't irrevocably fail, since most functions
-- are not theorems

rootProp (TyApp f y) = rootProp f
rootProp (TyCon l nm k) = Just nm
rootProp x = Nothing

isProp:: String -> Tau -> TC Bool
isProp new t =
  case rootProp t of
   Just s | s==new -> return True
   Just s -> isRuleCon s
   Nothing -> return False

getDomsRng (Rtau z) = Just(down [] z)
  where down xs (TyApp (TyApp (TyCon _ "(->)" _) x) y) = down (x:xs) y
        down xs z = (reverse xs,z)
getDomsRng r = Nothing


addTheorem :: String -> Frag -> Sigma -> TC Frag
addTheorem fname (frag@(Frag vs exs ts toenv theta rules)) sig =
  do { ((preds,rho),lhsRho) <- splitIntoPredsRho sig
     ; always <- newTau star
     ; case okRho rho of
        Just (tname,doms,rng) ->
            ifM (allM (isProp "") (rng:doms))
                (do { r2 <- sigmaToRWrule Theorem fname sig
                    ; return(Frag vs exs ts toenv theta ((rkey r2,r2):rules) )
                    })
                (return frag)
        Nothing -> return frag
     }

okRho :: Rho -> Maybe(String,[Tau],Tau)
okRho rho =
  do { (doms,rng) <- getDomsRng rho
     ; tname <- rootProp rng
     ; return(tname,doms,rng)}

-----------------------------------------------------------
-- splitRho(S a -> T a -> Q a) = ([S a,T a],Q a)

splitRho (Rtau z) = return(down [] z)
  where down xs (TyApp (TyApp (TyCon _ "(->)" _) x) y) = down (x:xs) y
        down xs z = (reverse xs,z)
splitRho r = failD 1 [Ds "Non trivial rho type in proposition: ",Dd r]

nullM x y z = do { xs <- x; if null xs then y else z}

------------------------------------------------------------------------------

solveEqAssump :: DispInfo Z -> Tau -> Tau -> TC (Maybe Result)
solveEqAssump d1 x y =
  case mgu [(x,y)] of
    Left [] -> return Nothing
    Left [(v,t)] -> return Nothing -- (Just[Rel "(!=)" (notEq (TcTv v) t)])
    Left xs -> failD 1 [Ds "More than one residual in in-equality",Dl xs ", "]
    Right _ -> return (Just(Rs d1 [] []))

solveEqual:: DispInfo Z -> Tau -> Tau -> TC(Maybe Result)
solveEqual d1 x y =
  do { a <- zonk x -- nf x
     ; b <- zonk y -- nf y
     ; let f (v,e) = equalRel (TcTv v) e
     ; case mgu [(a,b)] of
        Left [] -> return(Just(Rs d1 [] []))
        Left xs -> return Nothing
        Right(s,m,n) -> failD 3 [Ds "The Equality constraint: "
                                ,Dd x, Ds " = ",Dd y
                                ,Ds "Cannot be solved\n"
                                ,Ds s]}

instance Eq Pred where
  (Equality a b) == (Equality x y) = a==x && b==y
  (EqAssump a b) == (EqAssump  x y) = a==x && b==y
  (Rel x) == (Rel y) = x==y
  _ == _ = False

-------------------------------------------------------------
-- Split the propositions into two lists, those that can be
-- found under some unifier that matches at least one MutVar.

mightMatch :: [Pred] -> (MGU,[Pred]) -> (MGU,[Pred],[Pred])
mightMatch truths (un,[]) = (un,[],[])
mightMatch truths (un,x:xs) =
  case mightMatch truths (un,xs) of
   (un2,good,bad) ->
       case oneMatch2 (Left un2) truths x of
        Just un3 | all has1Mut un3 -> (un3,x:good,bad)
        Just un3 -> (un2,good,x:bad)
        Nothing -> (un2,good,x:bad)

oneMatch2 :: (Either [(TcTv,Tau)] (String,Tau,Tau)) -> [Pred] -> Pred -> Maybe MGU
oneMatch2 un1 [] x = Nothing
oneMatch2 un1 ((Rel t):ts) (z@(Rel x)) =
  case mgu [(x,t)] of
    Right _ -> oneMatch2 un1 ts z
    un2 -> case compose un2 un1 of
             Right _ -> oneMatch2 un1 ts z
             Left un3 -> Just un3
oneMatch2 un1 (t:ts) z = oneMatch2 un1 ts z

has1Mut (Tv u (Flexi _) k,_) = True
has1Mut (_,TcTv(Tv u (Flexi _) k)) = True
has1Mut _ = False

removeAlreadyTrue :: [Pred] -> [Pred] -> TC [Pred]
removeAlreadyTrue truths preds =
  do { let (unifier,good,bad) = mightMatch truths ([],preds)
     --; outputString ("\nBefore "++show unifier)
     ; mutVarSolve unifier
     ; u2 <- zonk unifier
     --; outputString ("\nAfter  "++show u2)
     ; return bad
     }


----------------------------------------------------------

thrd e1 f [] = return(e1,[])
thrd e1 f (x:xs) = do { (e2,y) <- f x e1; (e3,ys) <- thrd e2 f xs; return(e3,y:ys)}

getInfo y [] s = failD 1 [Ds "While checking the lhs: ",Dd y,Ds " unknown type: ",Dd s]
getInfo y ((x,tau,k):xs) s = if s==x then return (tau,k) else getInfo y xs s

-- In order to kind-check a type function we need to compute that the
-- given kind is consistent with the LHS of each clause, and we also
-- need to build a ToEnv, so that we can correctly parse the RHS

checkPTBndr :: ToEnv -> (Tpat,Tau) ->  TC ToEnv
checkPTBndr current (Tvar s nm,k) =
  return[(s,TyVar nm (MK k),poly (MK k))]
checkPTBndr current (Tfun c xs,k) = checkPTBndr current (Tcon c xs,k)

checkPTBndr current (y@(Tcon (tag@('`':cs)) xs),TyCon _ "Tag" _) = return[]

checkPTBndr current (y@(Tcon c xs),k) =
  do {(tau,kind@(K sigma)) <- getInfo y current c
     ; let check1 [] rng = return(rng,[])
           check1 (x:xs) (Karr m n) =
             do { env1 <- checkPTBndr current (x,m)
                ; (rng,env2) <- check1 xs n
                ; return(rng,env1++env2)}
           check1 (x:xs) kind = failD 1 [Ds "The type: ",Dd y,Ds " is not well kinded"]
     ; (preds,kind2) <-  instanTy sigma
     ; when (not(null preds))
            (failD 1 [Ds "Non empty relational predicate list in type function use: ",Dd y])
     ; case kind2 of
         Rtau k2 -> do { (rng,newenv) <- check1 xs k2
                       ; unify rng k
                       ; return newenv}
         rho -> failD 1 [Ds "Rho type: ",Dd rho,Ds " for kind of ",Dd y]
     }
checkPTBndr current (Tstar n,Star m) | m==n+1 = return []
checkPTBndr current (y@(Tstar n),k) =
  do { let err disp message =
             failD 3 [Ds "\nWhile kind checking a type function.\n"
                     ,Dd y,Ds " :: ",Dd k,Ds " is not well formed for a lhs."
                     ,Ds message]
     ; handleM 3 (unify (Star (n+1)) k) err
     ; return [] }
checkPTBndr current (Tkarr x y,k) =
  do { env1 <- checkPTBndr current (x,k)
     ; env2 <- checkPTBndr current (y,k)
     ; return(env1++env2) }
checkPTBndr current (y,k) =
  failD 1 [Dd y,Ds " :: ",Dd k,Ds " is not well formed for a lhs."]



----------------------------------------------------

testRankN :: [[Dec]] -> FIO Z ([[Dec]])
testRankN dss = fio $ runTC tcEnv0 (letExtend nullFrag (testBndGroups dss))

parseAndKind :: TcEnv -> [Char] -> FIO Z (Kind,Tau)
parseAndKind env s = tcInFIO env
    (
    do { map1 <- getTypeEnv
       ; s <- toTau map1 (parsePT s)
       ; (tau::Tau,s2) <- infer s
       ; return(MK tau,s2)
       -- ; return(MK (kindOf s2),s2)
       })

genericEnv free = foldrM acc ([],[],[]) free
  where acc s (ts,vs,us) =
          do { k <- newTau star1
             ; tau@(TcTv u) <- newTau (MK k)
             ; return((s,tau,poly (MK k)):ts,(ZTv u,s):vs,u:us)}

-- Used for the :narrow command
narrowString env count s =
  do { map1 <- getTypeEnv
     ; (n,parseT) <- (parseIntThenType count s)
     ; let free = getFree [] parseT
     ; outputString (show free)
     ; (map2,vs,us) <- genericEnv free
     ; ty <- toTau (map1++map2) parseT
     ; (k::Tau,newTau) <- infer ty
     ; let d0 = (newDI vs)
           (d1,cntxt) = displays d0 [Dd newTau]
     ; (sols,(_,_,d1,ex)) <- narr cntxt (20,n,d1,False) [(TermP newTau,andR[],[])] []
     ; showSols d1 us (newToOld ex sols)
     ; return env
     }


showSols d0 free (Answers []) = return d0
showSols d0 free (Exceeded []) = warnD d0 [Ds "\n*** Narrowing resources exceeded. ***\n"]
showSols d0 free (Answers ((x,u):zs)) =
  do { d1 <- warnD d0 [Dd x,Ds "\n  ",Dl (trim free u) "\n  ",Ds "\n"]
     ; showSols d1 free (Answers zs) }
showSols d0 free (Exceeded ((x,u):zs)) =
  do { d1 <- warnD d0 [Dd x,Ds "\n  ",Dl (trim free u) "\n  ",Ds "\n"]
     ; showSols d1 free (Exceeded zs) }

trim free xs = filter p xs
  where p (nm,ty) = elem nm free


tt s = testTC tcEnv0 (narrowString 2 5 s)

testBndGroups :: [[Dec]] -> TC [[Dec]]
testBndGroups [] = return []
testBndGroups (ds:dss) =
  do { outputString ("Group Binds" ++ show(concat (map decname ds)));
       env <- getTypeEnv
     --; mapM g7 env
     ; (frag,ds2) <- inferBndrForDecs False ds
     --; showFrag "" frag
     -- ; (preds,unifier) <- fragMGU ("checking testBndGroups",starR) frag
     ; dss2 <- letExtend frag (testBndGroups dss)
     ; return(ds2:dss2)
     }

arrowP (Rarrow _ _) = True
arrowP (Rtau (TyApp (TyApp (TyCon l "(->)" k) x) y)) = True
arrowP _ = False

wellTyped :: TcEnv -> Exp -> FIO Z (Sigma,Exp)
wellTyped env e = tcInFIO env
  (do { ((t::Rho,term),oblig) <- collectPred(inferExp e)
      ; truths <- getAssume
      ; oblig2 <- solveConstraints (show e,t) truths oblig
      ; typ <- nfRho t
      ; when (not(null oblig2) && not(arrowP typ))
             (failD 0 [Ds "Unresolved obligations: ",Dl oblig2 ", "
                      , Ds " => ", Dd typ])
      -- ; warnD disp0 [Ds "\nt = ",Dd t2, Ds "\ntyp = ",Dd typ]
      ; sigma <- generalize(oblig2,typ)
      ; s2 <- return sigma -- nf sigma
      ; return(s2,term)})

ioTyped :: TcEnv -> Pat -> Exp -> FIO Z (Exp,Pat,TcEnv,Tau)
ioTyped env p e =
  tcInFIO env
    (do { a <- newTau star
        ; e' <- check e (Rtau (TyApp ioT a))
        ; (frag,p') <- checkBndr False Wob nullFrag (simpleSigma a) p
        ; a' <- zonk a
        ; return (e',p',addLetFrag frag env,a')
        })


tcInFIO :: TcEnv -> TC x -> FIO Z x
tcInFIO env e =
  do { (x,ns::[Pred]) <- unTc e env
     ; if null ns
          then return x
          else fail ("\nUnresolved NEED: "++show ns)}

showFrag message frag =
  do { (Frag xs rs tenv eqs theta rules) <- zonk frag
     ; outputString ("\n********** Frag ***************" ++ message ++
           "\nBindings = "++plistf showBind "" (take 5 xs) ", " ""++
           "\nSkolem = "++show rs++
           "\nTypeEnv = "++ show tenv++
           "\nPreds = "++showPred eqs++"\n*********************") }


dispFrag d message frag =
   do { (Frag xs rs tenv eqs theta rules) <- zonk frag
      ; warnD d [Ds ("\n********** Frag ***************" ++ message)
                ,Ds "\nBindings =\n  ",Dlf dispBind (take 5 xs) "\n  "
                ,Ds "\nSkolem = ",Dl rs ", "
                -- ,Ds "\nTypeEnv = ",Dd tenv
                ,Ds "\ntheta = ",Dl theta ", "
                ,Ds "\nPreds = ", Dl eqs "; "]}


showBind (x,(t,mod,_,_)) = show x ++":"++show t
dispBind d (x,(t,mod,_,_)) = displays d [Dd x,Ds ":",Dd t]

g7 (s,mod,t,k) = outputString ("type "++s ++" : " ++ alpha [] k)

----------------------------------------------------------------------
-- The interactive type checking loop
-- Loop until "f" says quit (continue == True), catch all errors
-- but continue looping after reporting them

interactiveLoop :: (env -> state -> TC(state,Bool)) -> env -> state -> TC state
interactiveLoop f env info = handleM 3
  (do { (info2,continue) <-  (f env info)
      ; if continue then interactiveLoop f env info2 else return info2
      }) (\ dis s -> do {outputString s; interactiveLoop f env info})

-- use the ReadLine library to enable line editing
-- pass a prompt and a tab expansion function

lineEditReadln :: String -> (String -> [String]) -> FIO Z String
lineEditReadln prompt expandTabs = fio body
 where body = do { Readline.setCompletionEntryFunction(Just (return . expandTabs))
                 ; s <- Readline.readline prompt
                 ; let addHist Nothing = return ""
                       addHist (Just "") = return ""
                       addHist (Just s) = (Readline.addHistory s)>>(return s)
                 ; addHist s
                 }

setCommand "" value tenv =
    do { ms <- readRef modes
       ;  let f (mode,bool) = mode++" = "++show bool
       ; writeln (plistf f "" ms "\n" "\n")
       ; return tenv }
setCommand mode value tenv = setMode mode value >> return tenv

updateDisp :: DispInfo Z -> TC (DispInfo Z)
updateDisp x@(DI (bs,names)) = do {new <- reset bs; return(DI(new,names))}
  where reset [] = return []
        reset ((ZVar n k,s):xs) =
          do { ys <- reset xs; return((ZVar n k,s):ys)}
        reset ((ZTv v,s):xs) =
          do { ys <- reset xs
             ; tau <- prune(TcTv v)
             ; case tau of
                 TcTv u ->
                    case lookup (ZTv u) ys of
                      Nothing -> return((ZTv v,s):ys)
                      Just new -> return((ZTv v,new):ys)
                 tau -> return ys
             }



putS s = fio2Mtc(fio (putStrLn s))
getS prompt expandTabs = fio2Mtc(lineEditReadln prompt expandTabs)

wait = fio2Mtc(fio (getLine))

checkReadEvalPrint :: (Expected Rho,TcEnv) -> DispInfo Z -> TC (DispInfo Z,Bool)
checkReadEvalPrint (hint,env) info =
  do { let tabExpandFun = completionEntry env
     ; input <- getS "check> " tabExpandFun
     ; z <- parseString pCommand input
     ; case z of
        Left s -> do {putS s; return (info,True) }
        Right(x,rest) ->
         case x of
          (ColonCom "set" s) -> fio2Mtc(setCommand s True (info,True))
          (ColonCom "q" _) -> return (info,False)
          (ColonCom "rules" s) ->
             do { let rs = getRules s env
                ; info2 <- warnD info [Ds "rules\n",Dl rs "\n  "]
                ; return(info2,True)
                }
          (ColonCom "e" _) ->
             do { truths <- zonk (assumptions env)
                ; info2 <- warnD info [Ds "truths: ",Dd truths,Ds ("\n  "++shtt truths)]
                ; return (info2,True) }
          (ColonCom "h" _) ->
             do { info2 <- warnD info [Ds "Hint = ",Dd hint]
                ; return(info2, True)
                }
          (ColonCom "k" x) ->
             do { (k,t,tree) <- getkind x env
                ; putS (x++" :: "++(pprint k)++"\n" ++ pprint t ++ "\n"++tree)
                ; return (info,True) }
          (ColonCom "t" x) ->
             case getVar (Global x) env of
                Just(sigma,mod,lev,exp) ->
                   do { s1 <- zonk sigma
                      ; info1 <- updateDisp info
                      ; info2 <- warnD info1 [Ds (x ++ " :: "),Dd s1]
                      ; return (info2,True)}
                Nothing -> do { putS ("Unknown name: "++x); return (info,True)}
          (ColonCom "o" e) ->
             do { exp <- getExp e
                ; (t,exp2) <- inferExp exp
                ; t1 <- zonk t
                ; info1 <- updateDisp info
                ; info2 <- warnD info1 [Ds (show exp ++ " :: "),Dd t1]
                ; return (info2,True)
                }
          (ColonCom "try" e) ->
             do {  exp <- getExp e
                ; (_,oblig) <- collectPred(inDisplay info (tc exp hint))
                ; obs <- zonk oblig
                ; info2 <- updateDisp info
                ; info3 <- warnD info2 [Ds(show exp ++ " :: "),Dd hint]
                ; info4 <- whenDd (not (null oblig)) info3
                                  [Ds "Only when we can solve\n   ",Dd obs]
                ; return (info4,True)
                }
          (ExecCom exp) ->
             do { ((t,e2),oblig) <- collectPred(inDisplay info (inferExp exp))
                ; t2 <- zonk t
                ; obs <- zonk oblig
                ; info2 <- updateDisp info
                ; info3 <- warnD info2 [Ds(show exp ++ " :: "),Dd t2]
                ; info4 <- whenDd (not (null oblig)) info3
                            [Ds "Only when we can solve\n   ",Dd obs]
                ; return (info4,True)
                }
          other -> putS "unknown command" >> return (info,True)
     }

checkLoop :: Expected Rho -> DispInfo Z -> TcEnv -> TC (DispInfo Z)
{- ##### checkLoop typ d env = interactiveLoop "check>" checkReadEvalPrint (typ,env) d -}
checkLoop typ d env = interactiveLoop checkReadEvalPrint (typ,env) d


---------------------------------------------------------
-- display names in a more readable manner by maintaining
-- a list of readable names for each Var encountered.

inDisplay :: DispInfo Z -> TC a -> TC a
inDisplay disp (Tc f) = Tc g
  where g env = f (env{displayInfo = disp})


instance NameStore d => Exhibit d [(Var,(Sigma,Level,Exp))] where
  exhibit xs [] = (xs,"")
  exhibit xs ys = exhibitL exhibit xs ys "\n   "

instance NameStore d => Exhibit d (Var,(Sigma,Level,Exp)) where
  exhibit xs (v,(s,l,e)) = (zs,show v++": "++ans)
   where (zs,ans) = exhibit xs s

--------------------------------------------------------
-- INitializing the type environment
--------------------------------------------------------

---------------------------------------------------------------
---------------------------------------------------------------


trans0 s = (readName "In trans0: ") typeConstrEnv0 s

{-
parseSigma :: TyCh m => String -> m Sigma
parseSigma s = toSigma typeConstrEnv0 (parsePT s)

getrho :: TyCh m => [Char] -> m Rho
getrho s = toRho typeConstrEnv0 (parsePT s)
-}


toEnvX :: ToEnv
toEnvX =
  [( "[]",        listT,poly star_star)
  ,( "(,)",       pairT, poly (karr star (star_star)))
  ,( "()",        unitT, poly star)
  ,( "(->)",      arrowT, poly (karr star (star_star)))
  ,( "Atom",      atomT, kind4Atom)
  ,( "(+)",       sumT, poly (karr star (star_star)))
  ,( "(!=)",      notEqT, notEqKind)
  ,( "Hidden",    hiddenT, kind4Hidden)
  ,( "String",    stringT,poly star)
  ,( infixEqName, TyCon (lv 1) infixEqName equalKind, equalKind)
  --, declare tagT   -- ( "Tag"    , tagT, poly star1)
  --, declare labelT -- ( "Label"  , labelT, poly (karr (MK tagT) star))
  ]

predefined =
 "data Int = primitive\n"++
 "data Char = primitive\n"++
 "data Float = primitive\n"++
 "data ChrSeq = primitive\n"++
 "data Code (x::*0) = primitive\n"++
 "data Symbol = primitive\n"++
 "data IO (x::*0) = primitive\n"++
 "data Ptr (x::*0) = primitive\n"++
 "data Parser (x::*0) = primitive\n"++
 "kind Tag = primitive\n"++
 "data Label (t :: Tag) = primitive\n"++
 "data Bind (x::*0) (y::*0) = primitive\n"++
 "data Bool = True | False\n"++
 "data Maybe a = Just a | Nothing\n"++
 "kind Prop = Success\n"++
 "and:: Prop ~> Prop ~> Prop\n"++
 "{and Success x } = x\n"++
 "kind Nat = Z | S Nat\n"++
 --"prop Nat' t = Z where t=Z | exists y . S (Nat' y) where t = S y\n"++
 "prop Nat' :: Nat ~> *0 where\n"++
 "  Z:: Nat' Z\n"++
 "  S:: forall (a:: Nat) . Nat' a -> Nat' (S a)\n"++
 --"data Equal a b = Eq where a=b\n"++
 "data Equal :: forall (a:: *1) . a ~> a ~> *0 where\n"++
 "  Eq:: forall (b:: *1) (x:: b) . Equal x x\n"++
 "kind HasType = Has Tag *0\n"++
 "kind Row (x::*1) = RCons x (Row x) | RNil\n"++
 "data Monad m =\n"++
 "   Monad (forall a . a -> m a)\n"++
 "         (forall a b . m a -> (a -> m b) -> m b)\n"++
 "         (forall a . String -> m a)\n"



-- Parse the predefined data decls
-- then do a topological sort.
preDefDec = dss
  where (Right(Program ds,_)) = parse2 program predefined
        ds1 = case mapM gadt2Data ds of
                Right xs -> xs
                Left s -> error ("Syntax error in predefined declarations\n   "++s)
        (dss,pairs) = topSortR freeOfDec ds -- ds1

look = putStr (show (map (map f) preDefDec)) where f x = (show x) ++ "\n"

-- Go through each binding group in the topological sort
-- and transform the environment

decMany :: [[Dec]] -> TcEnv -> FIO Z TcEnv
decMany [] env = return env
decMany (ds:dss) env =
  do { (env2,_,_) <- checkDecs env ds
     ; rt_env <- elaborate None ds (runtime_env env2)  -- evaluate the list
     ; let env3 = (env2 { runtime_env = rt_env })
     ; decMany dss env3}


tcEnv0 = unsafePerformIO(runFIO (decMany preDefDec initEnv) errF)
  where initEnv = TcEnv Map.empty toEnvX [] 0 Z [] [] Map.empty Map.empty env0 [] disp0 []
        errF disp loc n s = error ("While initializing "++show loc++"\n"++s)

typeConstrEnv0 = type_env tcEnv0

look2 :: IO[()]
look2 = showAllVals 1000 tcEnv0

--------------------------------------------------------------
-- Translating Circuit expressions
--------------------------------------------------------------

okCircuitDec (Val loc (Pvar s) (Normal e) []) = Nothing
okCircuitDec d = Just d

allOk ds = f maybes
  where maybes = map okCircuitDec ds
        f [] = return ()
        f (Nothing : xs) = f xs
        f (Just d: xs) = fail ("Illegal binding in circuit:\n  "++show d)

hasMonoType (var,(Forall (Nil ([],Rtau t)),mod,_,_)) = return (var,t)
hasMonoType (var,x) = fail (show var++" does not have a monomorphic type")


toRep (TyCon l "Bit" k) = Var (Global "Bit")
toRep (TyCon l "Int" k) = Var (Global "Int")
toRep (TyCon l "Z" k) = Var (Global "Z")
toRep (TyApp (TyCon l "S" k) x) = App (Var (Global "S")) (toRep x)
toRep (TyApp (TyApp (TyCon l "(,)" k) x) y) =
  (App (App (Var (Global "Prod")) (toRep x)) (toRep y))
toRep (TyApp (TyApp (TyCon l "Vec" k) x) y) =
  (App (App (Var (Global "Vec")) (toRep x)) (toRep y))

appE [x] = x
appE (x:y:xs) = appE ((App x y):xs)

stringLit s = listExp (map (Lit . Char) s)
labelLit s = Lit(Tag s)

transForm (v,TyApp (TyCon l "Exp" k) t) = return ("Exp1",v,toRep t)
transForm (v,TyApp (TyApp (TyApp (TyCon l "Exp" k) c) row) t) = return ("Exp3",v,toRep t)
transForm (v,TyApp (TyCon l "Sig" k) t) = return ("Sig1",v,toRep t)
transForm (v,z) = fail (show v++"::"++show z++" is not a circuit type")

collect2 [] [] = return (0::Int,[])
collect2 ((nm1@(Global name),typ):xs) ((nm2,exp):ys) | nm1==nm2 =
  do { (n,zs) <- collect2 xs ys
     ; return (n+1,(n,name,typ,exp):zs) }
collect2 _ _ = fail "Names don't correspond with declarations in circuit"

-- ==========================================
-- the example we refer to in the comments in this code
--
-- circuit (change) out2 where
--    out1 = Delay Low out2
--    out2 = Xor change out1
--
-- which has the intermnediate form:
-- InterF 2 [change] out2 [(1,out1,Bit,Delay Low out2),(0,out2,Bit,Xor change out1)]
-- ==========================================

data InterForm = InterF Int [Var] Exp [(Int,String,Exp,Exp)]

allSameForm x [] = return []
allSameForm x ((y,v,t):xs) | x==y = do {ys <- allSameForm x xs; return((v,t):ys)}
allSameForm x ((y,v,t):xs) = failD 1 [Ds "The declaration for ",Dd v,Ds " doesn't match the other declarations"]

--tcCircuit :: [Var] -> Exp -> [Dec] -> Expected Rho -> Mtc Z TcEnv Pred Exp
tcCircuit vs e ds expect =
 do { allOk ds
    ; (frag,ds2) <- inferBndrForDecs localRename ds
    ; outputString ("\n\n"++show (Circ vs e ds)++"\n translates to \n")
    ; Frag env skols ts eqns theta rs <- zonk frag
    ; pairs <- mapM hasMonoType env -- pre-translation [(out1,Exp Bit),(out2,Exp Bit)]
    ; (triples@((form,_,_):_)) <- mapM transForm pairs
    ; name_type <- allSameForm form triples -- post-translation [(out1,Bit),(out2,Bit)]
    ; let name_body (Val loc (Pvar s) (Normal e) []) = (s,e)
    ; (m,info2) <- collect2 name_type (map name_body ds2)
    -- info2 ::[(Int,String,Exp(Rep t),Exp(t))]
    --         [(1,"out1",Bit,Delay Low out2)
    --         ,(0,"out2",Bit,Xor change out1)]
    ; let intermediateForm = (InterF m vs e info2)
    ; case form of
       "Exp1" -> circuit1 expect  intermediateForm
       "Exp3" -> circuitExp3 expect intermediateForm
       "Sig1" -> circuitSig1 expect intermediateForm
       tag -> failD 1 [Ds "Impossible, transForm doesn't return this tag: ",Dd tag]
    }

-- Each type of circuit will need a different kind of substitution applied
-- to each RHS and the (In TERM), Given "f" we can construct such a substitution

circuitSub :: (Int -> String -> Exp -> Exp) -> (Int,String,Exp,Exp) -> (Var,Exp)
circuitSub f (n,label,typ,body) = (Global label,f n label typ)

-- Then the substitution can be applied with this function

subNew subst (n,label,typ,exp) =
     do { exp1 <- subExp subst exp; return(n,label,typ,exp1) }

-- Make a substitution for (Exp t) forms
subExp1 xs = map (circuitSub f) xs
  where f n nm typ = appE [Var (Global "Var"),stringLit nm,typ]

-------------------------------------------------------------------
-- Translation for (Exp t) form. The example translates to the term
--
-- mkLet (mkDecl "out1" Bit (Delay Low (Var "out2" Bit))
--       (mkDecl "out2" Bit (Xor change (Var "out1" Bit))
--       (mkIn (Var "out2" Bit))))


circuit1 expect (InterF m vs e info2) =
 do { let substitution = (subExp1 info2)
    ; info3 <- mapM (subNew substitution) info2
    ; e2 <- subExp substitution e
    ; let declUp [] = App (var "mkIn") e2
          declUp ((n,label,typ,body):xs) =
             appE [var "mkDecl",stringLit label,typ,body,declUp xs]
          body = App (var "mkLet") (declUp info3)
    ; outputString ((show body)++"\n\n")
    ; e3 <- tc body expect
    ; return(e3)}

-------------------------------------------------------------------
-- Translation for (Exp c env t) form. The example translates to the term
--
--  RLet (Rdecl `out1 Bit (Delay Low (Var `out2))
--       (Rdecl `out2 Bit (Xor change (Sh(Var `out1)))
--       (Rin out2)))

-- Make a substitution for (Exp c env t) forms
subExp3 total xs = map (circuitSub shiftf) xs

shiftf n nm typ =
   shift n (appE [Var (Global "Var"),labelLit nm])

shift 0 e = e
shift n e = App (var "Sh") (shift (n-1) e)

circuitExp3 expect (InterF m vs e info2) =
 do { let substitution = (subExp3 m info2)++(map vf vs)
          vf (Global nm) = (Global nm,shiftf m nm undefined)
    ; info3 <- mapM (subNew substitution) info2
    ; e2 <- subExp substitution e
    ; let declUp [] = App (var "Rin") e2
          declUp ((n,label,typ,body):xs) =
              appE [var "Rdecl",labelLit label,typ,body,declUp xs]
          body = App (var "RLet") (declUp info3)
    ; outputString ((show body)++"\n\n")
    ; e3 <- tc body expect
    ; return(e3)}

-------------------------------------------------------------------
-- Translation for (Sig t) form. The example translates to the term
--
-- let monad monadM
-- in Sig(do { (nm1,out1) <- var "out1" Bit
--           ; (nm2,out2) <- var "out2" Bit
--           ; bindS nm1 Bit (delay Low out2)
--           ; bindS nm2 Bit (xor change out1)
--           ; unSig(out2)
--           })

gensym s = do { n' <- fresh
              ; return(Pvar(Alpha s n'),Var(Alpha s n'))}

circuitSig1 expect (InterF m vs e info2) =
 do { let gen (n,name,typ,body) =
            do { (p,e) <- gensym name; return(p,e,name,typ,body)}
          varf(p,e,name,typ,body) =
               BindSt Z (Pprod p (Pvar (Global name)))
                        (appE [var "var",stringLit name,typ])
          bindf(p,e,name,typ,body) =
               NoBindSt Z (appE[var "bindS",e,typ,body])
    ; info3 <- mapM gen info2
    ; let all = map varf info3 ++ map bindf info3 ++
                [NoBindSt Z (App (var "unSig") e)]
          term = Let [monadDec Z (var "monadM")] (App (var "Sig") (Do all))
    ; outputString ((show term)++"\n\n")
    ; e3 <- tc term expect
    ; return(e3)}


-----------------------------------------------------------
instance NameStore d => Exhibit d Pat where
  exhibit d1 (Plit c) = (d1,show c)
  exhibit d1 (Pvar s) = (d1,show s)
  exhibit d1 (Pprod x y) = (d2,"("++ xS ++","++ yS++")")
    where (d2,xS,yS) = exhibit2 d1 (x,y)
  exhibit d1 (Psum L x) = (d2,"(L "++ xS ++")") where (d2,xS) = exhibit d1 x
  exhibit d1 (Psum R x) = (d2,"(R "++ xS ++")") where (d2,xS) = exhibit d1 x
  exhibit d1 (Pexists x) = (d2,"(Ex "++ xS ++")") where (d2,xS) = exhibit d1 x
  exhibit d1 (Paspat x p) = (d2,"("++ xS ++ " @ " ++ pS ++ ")")
    where (d2,xS,pS) = exhibit2 d1 (x,p)
  exhibit d1 Pwild = (d1,"_")
  exhibit d1 (Pcon x []) = exhibit d1 x
  exhibit d1 (Pcon x ps) = (d3,"("++ xS ++ " " ++ listS++ ")")
    where (d2,xS) = exhibit d1 x
          (d3,listS) = exhibitL exhibit d2 ps " "
  exhibit d1 (Pann p t) = (d2,"("++ pS ++" :: "++ tS ++")")
    where (d2,pS,tS) = exhibit2 d1 (p,t)

instance  NameStore d => Exhibit d Var where
  exhibit d1 v = (d1,show v)


instance Exhibit (DispInfo Z) Lit where
  exhibit d1 c = (d1,show c)
instance Exhibit (DispInfo Z) Exp where
  exhibit d1 c = (d1,show c)


instance Exhibit (DispInfo Z) Constr where
  exhibit d (Constr _ targs c doms Nothing) =
    displays d [Ds "exists ",Dlf hf targs ",",Ds " . ",Ds (show c++" ")
               ,Dl doms ", "]
  exhibit d (Constr _ targs c doms (Just ps)) =
    displays d [Ds "exists ",Dlf hf targs ",",Ds " . ",Ds (show c++" ")
               ,Dl doms ", ",Ds " where ",Dl ps ", "]

hf d (Global s,pt) = displays d [Ds ("("++show s++","), Dd pt, Ds ")"]

instance Exhibit (DispInfo Z) RWrule where
  exhibit d (RW nm key rclass vars pre lhs rhs) =
    displays d [Ds (show rclass++" "++nm++": ")
               ,Dlg f "(exists " (foldr exf [] vars) "," ") "
               ,Ds "[", Dl pre ", ", Ds "] => ",Dd lhs,Ds " --> [",Dl rhs ", ",Ds "]"
              ]
   where f d (nm,k) = useStoreName nm k id d
         exf (nm,k,Ex) xs = (nm,k):xs
         exf (_,_,All) xs = xs



-------------------------------------------------------
-- mguBias only binds Skolem variables on the left, and
-- Flexi vars on the right. Skolem come from Fresh rules,
-- and the Flexi may appear in the goal being matched against.

mguBias :: [(Tau,Tau)] -> Either [(TcTv,Tau)] (String,Tau,Tau)
mguBias [] = Left []

mguBias ((TcTv (Tv n _ _),TcTv (Tv m _ _)):xs) | n==m = mguBias xs
mguBias ((TcTv (x@(Tv _ (Skol _) _)),tau):xs) = mguBiasVar x tau xs
mguBias ((tau,TcTv (x@(Tv n (Flexi _) _))):xs) = mguBiasVar x tau xs

mguBias ((TyApp x y,TyApp a b):xs) = mguBias ((x,a):(y,b):xs)
mguBias ((TyCon level_ s1 _,TyCon level_2 s2 _):xs) | s1==s2 = mguBias xs
mguBias ((Star n,Star m):xs) | n==m = mguBias xs
mguBias ((Karr x y,Karr a b):xs) = mguBias ((x,a):(y,b):xs)
mguBias ((x@(TyFun f _ ys),y@(TyFun g _ zs)):xs) | f==g = mguBias (zip ys zs ++ xs)
mguBias ((x@(TyVar s k),y):xs) = Right("No TyVar in MGUBias", x, y)
mguBias ((y,x@(TyVar s k)):xs) = Right("No TyVar in MGUBias", x, y)
mguBias ((TySyn nm n fs as x,y):xs) = mguBias ((x,y):xs)
mguBias ((y,TySyn nm n fs as x):xs) = mguBias ((y,x):xs)
mguBias ((x,y):xs) = Right("No Match in mguBias ", x, y)


mguBiasVar :: TcTv -> Tau -> [(Tau,Tau)] -> Either [(TcTv,Tau)] ([Char],Tau,Tau)
mguBiasVar x tau xs = if (elem x vs)
                         then Right("occurs check", TcTv x, tau)
                         else compose new2 (Left new1)
  where vs = tvsTau tau
        new1 = [(x,tau)]
        new2 = mguBias (subPairs new1 xs)

-----------------------------------------------------------
-- Narrowing

andKind = poly (karr prop (karr prop prop))

data NName
  = NTyCon String PolyKind
  | NTyApp
  | NStar Int
  | NKarr
  | NTyVar Name Kind
  | NSkol Integer String Kind


instance Eq NName where
 (NTyCon a b) == (NTyCon c d) = a==c
 NTyApp       == NTyApp       = True
 (NStar n)    == (NStar m)    = n==m
 NKarr        == NKarr        = True
 (NTyVar n k) == (NTyVar m _) = n==m
 (NSkol n s k) == (NSkol m _ _) = n==m
 _            == _            = False

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

instance NTerm Z NName TcTv Tau where
  projN = project
  injN = inject
  varN x = TcTv x
  subN = subTau
  mguN = mostGenUnify
  matchN = match
  success = TyCon (lv 1) "Success" (poly(MK propT))
  andName = NTyCon "and" andKind
  varWild (Tv _ _ k) = TcTv(wild k)
  termWild t = TcTv (wild (MK(kindOf t)))
  equalTerm = teq

  equalP (TyApp (TyApp (TyCon _ "Equal" k) x) y) = True
  equalP _ = False

  equalParts (TyApp (TyApp (TyCon _ "Equal" k) x) y) = (x,y)

  dterm = Dd
  dname = Dd
  dvar = Dd



  samples = error "No samples method"
  toName x = error "No toName method"
  varF n = error "No varF method"

instance Speaks (Mtc Z TcEnv Pred) Z where
  wait = do { line <- getS "press return to step, 'c' to continue:\n" (\ _ -> [])
            ; case line of
                "c" -> setMode "steps" False>> return ()
                _ -> return ()}
  forbidN = getMode "forbid_ambiguity"
  delayN = do { z <- getMode "delay_narrowing"; return z}
  showStepN = getMode "steps"
  whenDN = whenDd
  warnN = warn
  warnDN = warnD

instance NMonad Z NName TcTv Tau (Mtc Z TcEnv Pred) where
  termFresh t = newTau (MK(kindOf t))
  varFresh (Tv u f k) = newTau k
  treeOfN = getDefTree
  normN = nfTau
  rewN = tryRewriting
  rewEqN = rewEq
  -- Some rules look like (Equal (Equal a b) c)
  rewNestedEqual (t1,t2) =
    do { rs <- getLemmaRules "Equal";
       ; applyLemmas rs (eqf t1 t2) }





instance Show (Kind -> TcTv) where
  show s = "Kind -> TcTv"
wild = testTC tcEnv0 (do { n <- nextInteger; r <- newRef Nothing; return(Tv n (Flexi r))})

defTreeInfo s =
 do { table <- getTyFuns
    ; let p (nm,f,tree) = nm==s
    ; return (find p table)
    }

getDefTree (NTyCon s _) =
 do { info <- defTreeInfo s
    ; case info of
        Just(nm,f,tree) -> return tree
        Nothing -> failD 0 [Ds "1) Unknown type function: ",Ds s]
    }
getDefTree other = failD 0 [Ds "Bad type function: ",Ds (show other)]

--  normalizes a TyFun term by "match"ing it against all the
-- leaves in the DefTree for that function. "applyTree" is written
-- in continuation passing style (at the computation level)
-- It also applys lemmas if no function definition matches.

normTyFun :: String -> PolyKind -> [Tau] -> TC Tau
normTyFun "(==)" k [x,y] = return(TyFun "(==)" k [x,y])
normTyFun s k ts =
   do {norm_ts <- mapM nf ts
      ; let new = (TyFun s k norm_ts)
            found (nm,f,tr) = return tr
            notFound = (failD 0 [Ds "2) Unknown type function: ",Ds s])
            doesn'tWork new =
               do { rs <- getLemmaRules s
                  ; maybeM (applyLemmas rs new)
                        (\ (newer,u2) -> return newer)
                        (return new)}
      ; tree <- maybeM (defTreeInfo s) found notFound
      ; applyTree tree new (doesn'tWork new)
      }

normEqual x y =
  do { x1 <- nf x
     ; y1 <- nf y
     ; rs <- getLemmaRules "Equal"
     ; warn [Ds "\nTrying normEqual on ",Dd x ,Ds " == ",Dd y]
     ; let new = (eqf x1 y1)
     ; maybeM (applyLemmas rs new)
              (\ (newer,u2) -> return newer)
              (return new)}


applyTree :: (DefTree TcTv Tau) -> Tau -> TC Tau -> TC Tau
applyTree (Leaf pat free lhs rhs) term next =
 do { (lhs2,rhs2) <- freshX (free,lhs,rhs)
    ; case match [] [(lhs2,term)] of
        Just unifier ->
           do { let rewritten = subN unifier rhs2
              ; verbose <- getMode "steps"
              ; whenDd verbose disp0 [Ds "Norm ",Dd term, Ds " ---> ", Dd rewritten,Ds "\n"]
              ; nf rewritten }
        Nothing -> next }
applyTree (Branchx pattern path trees) term next = first trees term
  where first [] term = next
        first (t:ts) term = applyTree t term (first ts term)


junk = poly(MK(TyCon (lv 0) "JUNK" undefined))


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
inject (RelN (EqR(x,y))) = equalTerm x y

prop = MK propT

---------------------------------------------------------------

instance NameStore d => Exhibit d (DefTree TcTv Tau) where
  exhibit d1 tree = indent 0 d1 tree

indent n d1 (Leaf term free lhs rhs )
   = (d3,blanks n ++ "Leaf " ++ lhsX++ " --> "++ rhsX)
     where (d2,lhsX) = exhibit d1 lhs
           (d3,rhsX) = exhibit d2 rhs
indent n d1 (Branchx term pos tree)
   = (d3,blanks n ++ "Branchx " ++ (show pos) ++ " " ++ termX++treeX)
     where (d2,termX) = exhibit d1 term
           (d3,treeX) = exhibitL (indent (n+1)) d2 tree ""

blanks n = "\n" ++ (take n (repeat ' '))

instance Show (DefTree TcTv Tau) where
  show x = y++"\n" where (disp2,y) = exhibit disp0 x

-----------------------------------------------------
-- mostGenUnify

type Unifier = [(TcTv,Tau)]

-- Given a set of truths and a set of predicates that ALL need to be
-- solved, If we can unify any of the predicates with a truth we can
-- remove it from the predicates needing solution. This makes the set
-- of things that must ALL be true smaller, But for each unifcation
-- we must duplicate the whole smaller problem. That is why we get a
-- list of smaller problems to solve. Solving any one of these will
-- solve the original problem. We should prefer solutions with the
-- most general unifiers (i.e. those that bind the fewest variables),
-- because these place fewer constraints on future steps.
-- This is why we sort. If a predicate matches exactly against a truth
-- (i.e. the unifier is the identity), any other other match of that
-- predicate against another truth should be removed, because it
-- is irrelevant to the solution, and could only lead the solver
-- down dead ends. For example when solving
-- [LE _c _a,LE _a _b] => LE _a _b,LE _c _a    we get the four possibilities
--   [LE _c _a,LE _a _b] => [LE _a _b] where {}
--   [LE _c _a,LE _a _b] => [LE _c _a] where {}
--   [LE _b _b,LE _b _b] => [LE _b _b] where {_c=_b, _a=_b}
--   [LE _c _c,LE _c _c] => [LE _c _c] where {_a=_c, _b=_c}
-- The second two are irrelevant since they are subsumed be the first two.

samePred (ts1,ps1,_,u1,i) (ts2,ps2,_,u2,j) = compare (i,length u1)(j,length u2)
moreGeneral (ts1,ps1,_,u1) (ts2,ps2,_,u2) = compare (length u1)(length u2)

relevant [] = []
relevant [(t,p,s,u,i)] = [(t,p,s,u)]
relevant (x@(_,_,_,[],i):y@(_,_,_,_,j):zs) | i==j = relevant (x:zs)
relevant ((t,p,s,u,i):zs) = (t,p,s,u):relevant zs

elim n [] = []
elim 0 (x:xs) = xs
elim n (x:xs) = x : (elim (n-1) xs)

truthStep :: ([Tau],[Tau],[String],Unifier) -> [([Tau],[Tau],[String],Unifier)]
truthStep (truths,questions,open,u0) =
      sortBy moreGeneral $
      relevant $
      sortBy samePred
      [ (map (subTau u) truths
        ,map (subTau u) (elim n questions)
        ,open,composeU u u0,n)
      | t <- truths
      ,(q,n) <- zip questions [0..]
      , u <- mostGenUnify [(t,q)] ]

---------------------------------------------------------------

ruleStep :: ([Tau],[Tau],[String],Unifier) -> TC(Maybe[([Tau],[Tau],[String],Unifier)])
ruleStep (truths,[],open,u0) = return Nothing
ruleStep (truths,q:questions,open,u0) =
   do { s <- predNameFromTau q q
      ; rules <- getMatchingRules s
      -- ; (warn [Ds "\nOpen rules: [",Dl open ",",Ds "], term is: ",Dd q, Ds ", Applicable rules are\n  ", Dl rules ",\n  ", Ds "\n"] >> wait )
      ; infoList <- matchR open rules q
      ; case infoList of
         [] -> do { zs <- ruleStep (truths,questions,open,u0)
                  ; return(fmap (map (f13 q)) zs)}
         ws -> return(Just(map (f14 u0 truths questions) ws))}
 where f13 q (ts,qs,nms,u) = (ts,(subTau u q):qs,nms,u)
       f14 u0 ts qs (pre,rhs,nms,u) = (fix ts,map (unRel 1) rhs ++ fix qs,nms,composeU u u0)
         where fix x = map (subTau u) x

composeU s1 s2 = ([(u,subTau s1 t) | (u,t) <- s2] ++ s1)
unRel n (Rel x) = x
unRel n x = error ("\nunRel applied to non Rel: "++show x++" "++show n)


exploreD n = length n > 3

matchR ::[String] -> [RWrule] -> Tau -> TC[([Pred],[Pred],[String],Unifier)]
matchR openRules [] term = return []
matchR open ((r@(RW nm key Theorem _ _ _ _)):rs) term | elem nm open = matchR open rs term
matchR open ((r@(RW nm key _ _ _ _ _)):rs) term | exploreD (filter (nm==) open) = matchR open rs term

matchR open ((r@(RW nm key cl _ _ _ _)):rs) term =
  do { (vars,precond,Rel lhs,rhs) <- freshRule newflexi r
     ; ys <- matchR open rs term
     ; case mostGenUnify [(lhs,term)] of
        Just sub -> do { let pre2 = subPred sub precond
                             rhs2 = subPred sub rhs
                       -- ; warn [Ds "Matching term against lhs: ",Dd term,Ds " returns ",Dd rhs2,Dd sub]
                       ; return((pre2,rhs2,nm:open,sub):ys) }
        Nothing -> return ys
     }


solv :: DispInfo Z -> Int -> [([Tau],[Tau],[String],Unifier)] -> TC ([([Tau],[Tau],[String],Unifier)],DispInfo Z)
solv d n [] = return ([],d)
solv d 0 xs = return ([],d)
solv d n ((ts,[],nms,u):xs) = do { (ys,d1) <- solv d (n-1) xs
                                 ; return ((ts,[],nms,u):ys,d1) }
solv d n ((x@(ts,qs,nms,u)):xs) =
  do { verbose <- getMode "verbose"
     ; d1 <- whenDd verbose d
             [Ds ("\n "++show n++" solving: ["),Dl ts ",",Ds "] => ",Dl qs ","]
     ; case truthStep x of
         [] -> do { m <- ruleStep x
                  ; case m of
                     Nothing -> do { (ys,d2) <- solv d1 (n-1) xs; return(x:ys,d2)}
                     Just ws ->
                       do { let f (truths,ques,_,_) = ques
                          ; d2 <- whenDd verbose d1 [Ds "Rule Steps\n  ",Dl (concat(map f ws)) "\n  "]
                          ; solv d2 n (xs++ws)}
                          }
         zs -> do { d2 <- whenDd verbose d1 [Ds "Truth Steps\n  ",Dlf f15 zs "\n  "]
                  ; solv d2 n (zs++xs)}}


f15 d (ts,qs,_,u) = displays d [Ds "[",Dl ts ",",Ds "] => [",Dl qs ",",Ds"]", Ds " where ",Dd u]


solvP :: [Tau] -> [Tau] -> TC([Pred],Unifier)
solvP truths questions =
  do { (ans,d1) <- solv disp0 4 [(truths,questions,[],[])]
     ; case ans of
         [] -> fail ("no solution to "++show truths++ " => "++show questions)
         [(ts,qs,nms,u)] -> return(map Rel qs,u)
         ((x@(ts,qs,nms,u)):xs) ->
           let aMostGeneral (ts,qs,nms,u) = null u
           in case find aMostGeneral (x:xs) of
                Just (ts,qs,nms,u) -> return(map Rel qs,u)
                Nothing -> do { z <- getMode "warn_ambiguity"
                              ; whenD z [Ds "Ambiguous solutions to [",
                                         Dl truths ",",Ds "] => [",Dl questions ",",Ds "]\n   ",
                                         Dlf g45 (x:xs) "\n   "]
                              ; return (map Rel qs,u)
                              }
     }

g45 d (ts,ps,nms,u) = displays d [Ds "questions [",Dl ps ",",Ds "] unifier ",Dd u,Ds " rules used ",Dl nms ","]


expandTruths truths =
  do { let (ps,eqs,un0) = split3 truths
     ; whenD (not (null eqs)) [Ds "Non null Narrowing questions in expandTruths:\n  ",Dl eqs ","]
     ; let un1 = applyDown [] un0
     ; let truths2 = map (subTau un1) ps
     ; zss <- mapM expandTau truths2
     ; return(concat zss)
     }

expandTau truth =
   do { s <- predNameFromTau truth truth
      ; rules <- getMatchingRules s
      ; checkTau rules truth
      }

checkTau :: [RWrule] -> Tau -> TC [Tau]
checkTau [] truth = return [truth]
checkTau ((r@(RW nm key Theorem _ _ _ _)):rs) truth = checkTau rs truth
checkTau ((r@(RW nm key Axiom _ _ _ _)):rs) truth =
  do { (vars,precond,Rel lhs,rhs) <- freshRule newflexi r
     ; ys <- checkTau rs truth
     ; case match [] [(lhs,truth)] of
        Just unifier -> do { let rhsts = map (unRel 33) rhs
                           ; return(map (subTau unifier) rhsts ++ ys)}
        Nothing -> return ys }

applyDown unifier [] = unifier
applyDown unifier ((v,t):xs) = applyDown u2 (map f xs)
  where u2 = (unifier++[(v,t)])
        f (v,t) = (v,subTau u2 t)

-----------------------------------------------------------------
-- To solve by narrowing we need some helper functions


lessTau (x,y) (a,b) = compare (count a+count b) (count x+count y)
   where count (TyFun nm k xs) = 0
         count (TyCon _ nm k) = 2
         count (Star n) = 2
         count (TySyn nm n fs vs x) = count x
         count x = 1

reportEnter p conj normf truths =
 do { verbose <- getMode "steps"
    ; whenDd verbose disp0
         [Ds "\n####################\nUnder: ",Ds (fst p)
         ,Ds "\nSolve By Narrowing: ", Dd conj
         ,Ds "\nNormal form: ",Dd normf
         ,Ds "\n with truths: ",Dd truths]}

reportExit d1 ans =
 do { truths <- getAssume
    ; verbose <- getMode "steps"
    ; whenDd verbose d1
             [Ds "\nAnswers = ", Dd ans,Ds "\nTruths = ",Dd truths]
    }

mentionsFree termL = ok
  where free = foldr union [] (map tvsTau (map (uncurry TyApp) termL))
        ok (v,term) = elem v free

collectEqAssump =
 do { truths <- getAssume
    ; let separate (EqAssump x y) ans = (x,y):ans
          separate x ans = ans
    ; return(foldr separate [] truths)}

checkKind (v@(Tv n f (MK k)), term) =
  do { term' <- check term k; return(v,term') }

newToOld ex ans = (if ex then Exceeded else Answers)(map g ans)
  where g (TermP x,ts,un) = (x,un)
        g (EqP(x,y),ts,un) = (eqf x y,un)


solveByNarrowing :: (Int,Int) ->(String,Rho) -> [Pred] -> [(Tau,Tau)] -> TC [(TcTv,Tau)]
solveByNarrowing (nsol,nsteps) context truths [] = return []
solveByNarrowing (nsol,nsteps) context@(s,_) truths xs =
    do { whenD False
              [ Ds ("\n***********************\nIn solve: "++s)
              , Ds "\nEquations = ",Dl xs "; "];
         tests <- zonk xs
       ; let ordered = sortBy lessTau tests
       ; let conj = andP(map EqP ordered)
             hyp = andR(map (EqR . pred2Pair) truths)
             originalVar = mentionsFree tests
       ; conj2 <- nf conj
       ; hyp2 <- nf hyp
       ; d1 <- reportEnter context conj conj2 truths
       ; let (d2,cntxt) = displays d1 [dProb d1 conj2]

       ; (ans2,(_,_,d3,exceed)) <- narr cntxt (nsteps,nsol,d2,False) [(conj2,hyp2,[])] []

       ; result <-
          case (newToOld exceed ans2) of
           Answers[(xinstan,unifier)] -> mapM checkKind (filter originalVar unifier)
           Answers[] -> failD 0 [Ds "The equations: ",Dd tests,Ds " have no solution"]
           Answers others -> moreThanOne context truths originalVar conj others
           Exceeded _ -> do {(d2,solvedByDecProc) <- tryCooper (map pred2Pair truths) conj d1
                            ; if solvedByDecProc
                                 then return[]
                                 else failD 0 [Ds "Solving the equations: ",Dd tests
                                              ,Ds " exceeded narrowing resources."]}
       ; reportExit d3 result
       ; zonk result}

mapfromDI (DI(xs,ys)) = foldr f [] xs
  where f (ZTv x,s) ans = (x,s):ans
        f _ ans = ans

tryCooper :: [(Tau,Tau)] -> Prob Tau -> DispInfo Z -> TC (DispInfo Z,Bool)
tryCooper truths x d1 =
  do { let xnorm = prob2Tau x
     ; truthsnorm <- nf truths
     ; xZonk <- zonk xnorm
     ; truthsZonk <- zonk truthsnorm
     ; let (d3,_) = displays d1 [Dd truthsZonk,Dd xZonk]
     ; case (toFormula (mapfromDI d3) truthsZonk xZonk) of
         Just (allform, form) ->
           do { d3 <- warnD d3 [Ds "\nUsing the decision procedure to check:\n"
                               ,Ds (show allform)]
              ; ans <-  handleM 3 (integer_qelim allform)
                         (\ d mess -> warn [Ds ("The decision procedure failed with the message: "++mess)]
                          >> return FalseF)

              ; case ans of
                  TrueF -> do { d4 <- warnD d3 [Ds "\nGOOD ans = ",Ds (show ans)]
                              ; return(d4,True)}
                  _ -> do { d4 <- warnD d3 [Ds "\nBAD ans = ",Ds (show ans)]
                          ; ans2 <- integer_qelim form
                          ; d5 <- warnD d4 [Ds "Non quantified =\n",Ds (show ans2)]
                          ; return (d5,False) }
              }
         Nothing -> return (d3,False)}

prob2Tau :: Prob Tau -> Tau
prob2Tau (TermP x) = x
prob2Tau (EqP(x,y)) = eqf x y
prob2Tau (AndP ps) = foldr1 andf (map prob2Tau ps)

pred2Pair (Equality x y) = (x,y)
pred2Pair (EqAssump x y) = (x,y)

moreThanOne context truths originalVar x others =
 do { d1 <- getDisplay
    ; (d2,solvedByDecisionProc) <- tryCooper (map pred2Pair truths) x d1
    ; case (x,solvedByDecisionProc) of
        (_,True) -> return []
        (EqP(x,y),_) ->
            (maybeM (useLemma (Equality x y))
                    (\ u -> exit x (Just u))
                    (exit x Nothing))
        (other,_) -> exit x Nothing}
 where proj (t,u) = filter originalVar u
       short = map proj others
       contextElem (name,Rtau(Star 0)) =
           Ds ("While infering the type for: "++name)
       contextElem (name,rho) =
           Dr [Ds ("\nWhile checking: "++name++":: "),Dd rho]
       exit origterm (Just u) = return u
       exit origterm Nothing = failD 2
          [contextElem context
          ,Ds "\nWe had to solve the narrowing problem:\n  "
          ,Dd origterm
          ,Ds "\nUnder the truths\n ",Dl truths "\n "
          ,Ds "\nBut, it has ambiguous solutions:\n  "
          ,Dl short "\n  "]

------------------------------------------------------------------
-- Once we have tried all possible backtracking, there comes a
-- point where me must incorporate the single solution into
-- the mutable state unifier. This is done by mguM,
-- this occurs in the TyCh monad (the M in mguM).

-- To add a set of predicates to the mutable unifier, solve
-- the complicated predicates getting simpler equations.
-- some of these equations bind mutable variables,
-- which can then be added.

mguM :: (String,Rho) -> [Pred] -> TC([Pred],[(TcTv,Tau)])
mguM p [] = return([],[])
mguM context@(s,r) preds =
  do { (other,hard,easy,unifier1) <- apply_mutVarSolve_ToSomeEqPreds preds

     ; d1 <- whenD False [Ds ("\nmguM "++s),Ds "\n preds = ",Dd preds
            ,Ds "\nother = ", Dl other ", "
            ,Ds "\nhard = ",Dl hard ", "
            ,Ds "\neasy = ",Dl easy ", "
            ,Ds "\n unifier1 = ",Dd unifier1]

     ; maybe <- unifierFromEasyTruths other easy
     ; (ps2,unifier2) <- case maybe of
                          Nothing -> failDd "mguErr" 2 disp0 [Ds "Contradiction"]
                          Just(hard,u) -> return(hard,u)
     ; let u3 = composeMGU unifier2 unifier1
           eqs = map (\ (Equality x y) -> (x,y)) (subPred u3 hard)
     -- ; warn [Ds "\nMGUM unifier2 = ",Dd unifier2,Ds " eqs = ", Dd eqs]
     ; truths <- getTruths
     ; u4 <- solveByNarrowing (3,25) ("4."++s,r) truths eqs
     ; let u5 = composeMGU u4 u3
     -- Failure of MutVarSolve means some kind of inconsistency
     -- Occurs check  when we have  (a = {plus a Z}) for example
     ; u6 <- mutVarSolve u5
     ; ps3<- zonk ps2
     ; ps4 <- sub ([],u6,[],[]) ps3 -- TODO LEVEL
{-
     ; warnD d2 [Ds "\nin MguM, preds = ",Dl preds ", "
                ,Ds "\nps4 = = ", Dl ps4 "; "
                , Ds "\n un6 = ", Dd u6]
-}
     ; return(ps4,u6)
     }

-- When given a function with a type function in its type, like:
-- half :: Nat' {plus n n} -> Nat' n
-- half Z = Z
-- we often need to solve things like (Equal Z {plus n n}) to get the
-- correct substitution [(n,Z)] to assume when typing the rhs. But we don't
-- want to spend many resources doing this. Generally either its easy
-- to do, or its not necessary. Sometimes while trying to find an easy
-- solution, we come up with a proof that the term is never solvable,
-- since these are things that are supposed to be true by assumption,
-- we have probably come across an unreachable case.


unifierFromEasyTruths hard [] = return(Just (hard,[]))
unifierFromEasyTruths hard ((h@(EqAssump x y)):ps) =
  do { d0 <- getDisplay
     ; let (d1,cntxt) = displays d0 [dProb d0 (EqP(x,y))]
     ; (sols,(_,_,d2,exceeded)) <- narr cntxt (10,2,d1,False) [(EqP(x,y),andR[],[])] []
     ; case (exceeded,sols) of
         (False,[]) -> return Nothing -- A contradiction !
         (False,[(term,truths,u1)]) ->  -- Where hoping if exceeded is True!!
              do { ps2 <- sub ([],u1,[],[]) ps
                 ; hard2 <- sub ([],u1,[],[]) hard
                 ; maybeM (unifierFromEasyTruths hard2 ps2)
                          (\ (hard3,u2) -> return(Just (hard3,composeMGU u2 u1)))
                          (return Nothing)} -- propogate contradictions
         (True,[(term,truths,u1)]) ->
              do { warnD d2 [Ds "\nWe ran out of narrowing resources solving:\n"
                         ,Dd h, Ds ".\nBut we found exactly one solution: "
                         ,Dd u1, Ds ".\nSo we are going to try it, anyway."]
                 ; ps2 <- sub ([],u1,[],[]) ps
                 ; hard2 <- sub ([],u1,[],[]) hard
                 ; maybeM (unifierFromEasyTruths hard2 ps2)
                          (\ (hard3,u2) -> return(Just (hard3,composeMGU u2 u1)))
                          (return Nothing)} -- propogate contradictions
         other -> maybeM (unifierFromEasyTruths hard ps)
                         (\ (hard4,u4) ->
                              do { h4 <- sub ([],u4,[],[]) h
                                 ; return(Just(h4:hard4,u4))})
                         (return Nothing)} -- propogate contradictions



-------------------------------------------------------------------------------

instance Exhibit (DispInfo Z) Mod where
  exhibit d Wob = (d,"Wobbly")
  exhibit d Rig = (d,"Rigid")

instance Exhibit (DispInfo Z) a => Exhibit (DispInfo Z) (Prob a) where
  exhibit d (TermP x) = exhibit d x
  exhibit d (EqP(x,y)) = displays d [Ds "Equal (",Dd x,Ds ") (",Dd y,Ds ")"]
  exhibit d (AndP xs) = displays d [Ds "and(",Dl xs ",",Ds ")"]

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


instance Exhibit (DispInfo Z) a => Exhibit (DispInfo Z) (Rel a) where
  exhibit d (EqR(x,y)) = displays d [Ds "Equal (",Dd x,Ds ") (",Dd y,Ds ")"]
  exhibit d (AndR xs) = displays d [Ds "and(",Dl xs ",",Ds ")"]

instance TypeLike m a => TypeLike m (Rel a) where
  sub env (EqR(x,y)) = do { a <- sub env x; b <- sub env y; return (EqR(a,b)) }
  sub env (AndR xs) = do { as <- mapM (sub env) xs; return (AndR as) }

  zonk (EqR(x,y)) = do { a <- zonk x; b <- zonk y; return (EqR(a,b)) }
  zonk (AndR xs) = do { as <- mapM (zonk) xs; return (AndR as) }

  get_tvs (EqR(x,y)) = binaryLift unionP (get_tvs x) (get_tvs y)
  get_tvs (AndR xs) = get_tvs xs

  nf (EqR(x,y)) = do { a <- nf x; b <- nf y; return (EqR(a,b)) }
  nf (AndR xs) = do { as <- mapM (nf) xs; return (AndR as) }

--------------------------------------------------------------------

mguWithFail:: Monad m => [(Tau,Tau)] -> m [(TcTv,Tau)]
mguWithFail xs =
  case mgu xs of
        Left sub -> return sub
        Right (mess,t1,t2) -> fail mess


findCommon xs [] = (xs,[],[])
findCommon xs (y:ys) = if null ps then (xs2,y:ys2,ps2) else (xs2,ys2,ps++ps2)
   where (xs1,ps) = g xs y
         (xs2,ys2,ps2) = findCommon xs1 ys
         g [] (a,b) = ([],[])
         g ((c,d):xs) (a,b) =
            if a==c
               then (xs,[(a,d,b)])  -- Assume each c in ((c,d):xs) appears at most once
               else let (ws,pairs) = g xs (a,b)
                    in ((c,d):ws,pairs)

mergeMgu :: [(TcTv,Tau)] -> [(TcTv,Tau)] -> Either [(TcTv,Tau)] (String,Tau,Tau)
mergeMgu sub1 sub2 =
  case findCommon sub1 sub2 of
   (_,_,[]) -> Left(composeU sub1 sub2)
   (sub1',sub2',triples) ->
      let project1(v,t1,t2) = (t1,t2)
          project2 sub (v,t1,t2) = (v,subTau sub t2)
      in case mgu (map project1 triples) of
           Right x -> Right x
           Left sub3 -> case mergeMgu sub3 (composeU sub1' sub2') of
                          Left us -> Left(us ++ map (project2 sub3) triples)
                          Right x -> Right x

a1 = [("a",12),("b",34),("c",23)]
a2 = [("z",1),("a",22),("c",11),("e",99)]

