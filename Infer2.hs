-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Mon Nov 13 16:07:17 Pacific Standard Time 2006
-- Omega Interpreter: version 1.3

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
import RankN(Sht(..),sht,univLevelFromPTkind
            ,Quant(..),TcTv(..),Tau(..),Rho(..),Sigma(..),Kind(..),PolyKind(..)
            ,ForAllArgs,ToEnv,PPred,PT(..),MGU,Unifier,Z(..),Expected(..),L(..)
            ,Pred(..),PPred(..),Flavor(..),Level(..)
            ,TyCh(..),TypeLike(..),Typable(..),Exhibit(..),NameStore(..),Subsumption(..)
            ,failD,failK,failM,warnM,handleM,whenM
            ,dispRef,subTau,subRho
            ,mguStar,star1,star,star_star,starR,splitU,shtt
            ,newKind,newSigma,newFlexiTyVar,newRigidTyVar,newTau,newRigid,newRho,newflexi
            ,existsInstance,rigidInstance,rigidInstanceL,generalize,instanL,newSkolem
            ,instanTy,instanPatConstr,checkArgs
            ,mgu,mostGenUnify,unify,morepolySS,match,alpha,morepolySigmaRho
            ,sigmaPair,sigmaSum,unifyCode,unifyFun
            ,poly,simpleSigma,toSigma,toTau,toEqs,toRho
            ,windup,unsafeUnwind,unBindWith,unwind,varsOfTau,varsOfPred
            ,getFree,getFreePredL,subPred,subpairs,disp0,lv,subst
            ,boolT,unitT,tlist,tpair,tunit',tsum,tcode,ioT,arrow,applyT,applyT',listT
            ,pairT,arrowT,kind4Atom,atomT,sumT,notEqKind,notEqT,propT,intT,charT
            ,ptsub,karr,chrSeqT,symbolT,floatT,ttag,tlabel,tarr
            ,kind4Hidden,hiddenT,stringT,equalKind,infixEqName,tvsTau,subPairs,teq
            ,argsToEnv,binaryLift,expecting,bindtype,failtype,zap,split3,rootT
            ,exhibitL,apply_mutVarSolve_ToSomeEqPreds
            ,parsePT,mutVarSolve,compose,equalRel,parseIntThenType,nfRho,showPred
            ,prune,pprint,readName,exhibit2,injectA)
--hiding (Level)
import List((\\),partition,sort,sortBy,nub,union,unionBy
           ,find,deleteFirstsBy,groupBy,intersect)
import Encoding2
import Auxillary(plist,plistf,Loc(..),report,foldrM,foldlM,extend,extendL,backspace,prefix
                ,DispInfo(..),Display(..),newDI,dispL,disp2,disp3,disp4,tryDisplay
                ,DispElem(..),displays,ifM,anyM,allM,maybeM,dv)
import LangEval(vals,env0,Prefix(..),elaborate)
import ParserDef(pCommand,parseString,Command(..),getExp)
import Char(isAlpha,isUpper)
import ParserDef(parse2, program,pd)
import System.IO.Unsafe(unsafePerformIO)
-- import IOExts(unsafePerformIO)
import SCC(topSortR)
import Cooper(Formula(TrueF,FalseF),Fol,Term,toFormula,integer_qelim,Formula)

import qualified System.Console.Readline as Readline

import qualified Data.Map as Map
   (Map,empty,member,insertWith,union
   ,fromList,toList,lookup)

import NarrowData(DefTree(..),NName(..),Rule(..),Prob(..),NResult(..),Rel(..)
                 ,andR,andP,andf,freshX,dProb,equalPartsM)
import Narrow(narr,defTree,Check(..))

------------------------------------------------------------
-- In order to instantiate the narrowing code we must supply
-- several functions that interact with the type-checking
-- monad. This is done by supplying the following instance.

instance Check (Mtc TcEnv Pred) where
  getMode s = getM s False
  wait = waitN  -- warnM [Ds "<return> to continue ..."] >> fio2Mtc(fio (getLine))
  rewNestedEqual (t1,t2) =
    do { rs <- getLemmaRules "Equal";
       ; applyLemmas rs (teq t1 t2) }
  getDefTree (NTyCon s _) =
    do { info <- defTreeInfo s
       ; case info of
           Just(nm,tree) -> return tree
           Nothing -> failM 0 [Ds "1) Unknown type function: ",Ds s] }
  getDefTree other = failM 0 [Ds "Bad type function: ",Ds (show other)]
  tryRewriting t =
    do { (t2,u) <- rew t
       ; if t==t2 then return Nothing else return (Just (t2,u))};
  rewEq (t1 @(TyFun nm k xs),t2) =
            do {rs <- getLemmaRules nm; try True (t1,t2) rs}
    where try True (t1,t2@(TyFun nm k xs)) [] =
            do { rs <- getLemmaRules nm; try False (t2,t1) rs }
          try other (t1,t2) [] = return Nothing
          try other (t1,t2) ((lemma,(vs,[],lhs,rhs)):more) =
            case match [] [(lhs,t1),(rhs,t2)] of
              Just u -> do { warnM [Ds ("\n*** Trying equality lemma '"++rname lemma)
                                  ,Ds "' on term:\n   ",Dd (teq t1 t2)]
                           ; return (Just [])} -- matching means no variables escape
              Nothing -> try other (t1,t2) more
          try other (t1,t2) (m:more) = try other (t1,t2) more
  rewEq (_,_) = return Nothing



---------------------------------------------------------------------------------------
-- In a similar fashion in order to instantiate the RankN code we must supply
-- a few functions by supplying an instance for TyCh

instance TyCh (Mtc TcEnv Pred) where
   envTvs = do { (vs,triples) <- getVarsFromEnv; return vs}
   handleK = handleTC
   assume preds unifier m =
        do { env <- tcEnv
           ; let env2 = env { bindings = composeMGU unifier (bindings env)
                            , assumptions = preds ++ (assumptions env) }
           ; inEnv env2 m
           }
   getBindings = getBs
   getDisplay = readRef dispRef
   normFun = normTyFun
   normEq = normEqual

   solveSomeEqs = mguM

   show_emit = getMode "predicate_emission"
   getTruths = getAssume
   setTruths = setAssumptions
   -- peekPred = peek
   currentLoc = getLoc

type TC a = Mtc TcEnv Pred a


----------------------------------------------
-- Operations on Display

mapfromDI (DI(xs,_,ys)) = foldr f [] xs
  where f (ZTv x,s) ans = (x,s):ans
        f _ ans = ans

showThruDisplay elems =
  do { d0 <- readRef dispRef
     ; let (d1,cntxt) = displays d0 elems
     ; writeRef dispRef d1
     ; return (d1,cntxt)}


registerDisp :: TyCh m => String -> TcTv -> m String
registerDisp name rigid =
 do { d0 <- readRef dispRef
    ; let (d1,name2) = tryDisplay 1 name name (ZTv rigid) (\x -> "_"++x) d0
    ; writeRef dispRef d1
    ; return name2 }

-------------------------------------------------------------------------------------
-- Operations Maps

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

inEnv :: TcEnv -> TC c -> TC c
inEnv env (Tc f) = Tc(\ x -> f env)

tcEnv :: TC TcEnv
tcEnv = (Tc (\ env -> return(env,[])))

getBs = do { env <- tcEnv; zonk(bindings env) }
getAssume = do { env <- tcEnv; zonk(assumptions env) }
collectPred :: TC a -> TC (a,[Pred])
collectPred x = do { (ans,ps) <- extractAccum x; ps2 <- zonk ps; return(ans,ps2) }

getMatchingRules s = do { env <- tcEnv; return(getRules s env)}

instance TracksLoc (Mtc TcEnv Pred) Z where
  position = do { l <- getLoc; return l}
  failN loc n k s = Tc h
    where h env = FIO(return(Fail loc n k s))

-------------------------------------------------------------------------
-- The type checking environment TcEnv and its auxillary data types

data Mod = Wob | Rig deriving (Eq,Show) -- a Modifier is either Wobbly or Rigid
type CodeLevel = Int
type Refutation = Tau -> TC ()

-- The type of the internal environment of the Type Checking Monad
data TcEnv
  = TcEnv { var_env :: FiniteMap Var (Sigma,Mod,CodeLevel,Exp) -- Term Vars
          , type_env :: [(String,Tau,PolyKind)] -- Type Vars
          , generics :: [(Var,Sigma)]    -- Lambda Bound Names
          , level :: CodeLevel           -- code level, counts brackets
          , location :: Loc              -- position in file
          , bindings :: MGU              -- equality bindings
          , assumptions :: [Pred]        -- assumptions
          , rules :: FiniteMap String [RWrule] -- Proposition simplifying rules
          , refutations :: FiniteMap String Refutation
          , runtime_env :: Ev            -- current value bindings
          , imports :: [(String,TcEnv)]  -- already imported Modules
          , tyfuns :: [(String,DefTree TcTv Tau)]
          }

tcEnv0 = unsafePerformIO(runFIO (decMany preDefDec initEnv) errF)
  where initEnv = TcEnv Map.empty toEnvX [] 0 Z [] [] Map.empty Map.empty env0 [] []
        errF loc n s = error ("While initializing "++show loc++"\n"++s)

typeConstrEnv0 = type_env tcEnv0
initTcEnv = addFrag frag0 tcEnv0

frag0 = Frag (map f vals) [] [] [] [] []
  where f (nm,(v,sigma)) = (Global nm,(sigma,Rig,0,Var (Global nm)))

-- Used for adding simple Frags, where we don't expect things like theorems etc.

addFrag (Frag pairs rigid tenv eqs theta rs) env = extend env
  where extend env = env { var_env = addListToFM (var_env env) pairs
                         , bindings = composeMGU theta (bindings env)
                         , rules = appendFMmany (rules env) rs
                         , type_env = tenv ++ (type_env env)
                         }

--------------------------------------------------------
-- setting and using Bounds

boundRef = unsafePerformIO $
  do { narrow <- newRef (25::Int)
     ; backchain <- newRef 4
     ; return
        [("narrow"   ,"   Number of steps to take when narrowing.",narrow)
        ,("backchain"," Number of times a backChain lemma can be applied.",backchain)
        ]
     }

getBound s m =
  case find (\ (nm,info,ref) -> nm==s) boundRef of
    Just(_,_,ref) -> readRef ref
    Nothing -> return m


--------------------------------------------------------
-- using Modes

modes_and_doc =
  [("solving",False,"Turns on tracing in the predicate solving engine.")
  -- ,("delay_narrowing",True,"When narrowing an equality such as (v = {\\tt \\{plus a b\\}}), binds the variable 'v' to {\\tt \\{plus a b\\}}, rather than narrowing the variable 'a' to constructors. The binding is then emitted as predicate to be solved later. This has the effect of delaying narrowing until more is known about 'v', 'a', or 'b'.")
  ,("predicate_emission",False,"Reports the fact that a prediciate has been emitted. Predicates are collected at generalization sites, and are either solved, or abstracted into constrained types.")
  ,("narrowing",False,"Shows the steps taken when narrowing. Useful for debugging when narrowing does not return the result desired.")
  ,("theorem",False,"Reports when a lemma is added by a 'theorem' declaration, and when such a lemma is applicable.")
  ]

mode0 = map (\ (name,value,doc) -> (name,value)) modes_and_doc
tcEnvEmpty = TcEnv Map.empty toEnvX [] 0 Z [] [] Map.empty Map.empty env0 [] []

modes ::  IORef [(String,Bool)]
modes = unsafePerformIO(newIORef mode0)

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

----------------------------------------------------------------
-- simple operations on Frag

-- type ToEnv = [(String,Tau,PolyKind)] -- In RankN.hs
data Frag = Frag [(Var,(Sigma,Mod,CodeLevel,Exp))] [TcTv] ToEnv
                 [Pred] Unifier [(String,(RWrule))]

interesting (Frag env skols _ eqn theta rules) = not(null eqn)

nullFrag = Frag [] [] [] [] [] []

-- One can perform substitution and zonking on Frags

instance TypeLike (Mtc TcEnv Pred) Frag where
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

composeM (env@(_,s1,_,_)) s2 =
 do { let f (v,t) = do { t2 <- sub env t; return(v,t2) }
    ; prefix <- mapM f s2
    ; return(prefix ++ s1)}

infixr +++    --- NOTE (+++) is NOT COMMUTATIVE, see composeU
(Frag xs ys zs eqs u1 rs1) +++ (Frag as bs cs eqs2 u2 rs2) =
  case (mergeMgu u1 u2) of
    Left u3 -> return (Frag (xs++as) (ys++bs) (zs++cs) (eqs ++ eqs2) u3 (rs1++rs2))
    Right (mess,t1,t2) -> failD 2 [Ds "Inconsistent types checking patterns: "
                               ,Dd t1,Ds " != ", Dd t2]

composeU s1 s2 = ([(u,subTau s1 t) | (u,t) <- s2] ++ s1)

-- adding things to Frags

addPred :: [Pred] -> Frag -> TC Frag
addPred truths (Frag xs ys zs eqs theta rs) = return(Frag xs ys zs (truths++eqs) theta rs)

addEqs ps (Frag terms pvs types eqs theta rules)  =
          (Frag terms pvs types (subPred theta (ps ++ eqs)) theta rules)

addSkol :: [TcTv] -> Frag -> Frag
addSkol vs (Frag xs ys zs eqs theta rs) = Frag xs (vs++ys) zs eqs theta rs

addTermVar p@(v,(Forall(Nil ([],Rtau tau)),m,l,e))
           frag@(Frag terms pvs types eqs theta rules) =
   ifM (isProp "" tau)
       (return (addEqs [(Rel tau)] (Frag (p:terms) pvs types eqs theta rules)))
       (return (Frag (p:terms) pvs types eqs theta rules))
addTermVar p (Frag terms pvs types eqs theta rules) =
       (return (Frag (p:terms) pvs types eqs theta rules))

addUnifier u (Frag terms pvs types eqs theta rules) =
   case (mergeMgu u theta) of
     Left u2 -> return(Frag terms pvs types eqs u2 rules)
     Right(s,t1,t2) -> failD 2 [Ds "Inconsistent types checking patterns: "
                               ,Dd t1,Ds " != ", Dd t2]

addPVS vs (Frag terms pvs types eqs theta rules) =
          (Frag terms (vs++pvs) types eqs theta rules)

addRules rs (Frag terms pvs types eqs theta rules) =
            (Frag terms pvs types eqs theta (rs ++ rules))

-- using Frags

applyTheta Rig (Frag terms pvs types eqs theta rules) term = sub ([],theta,[],[]) term
applyTheta Wob frag term = return term

-- extracting elements of a Frag

getToEnv (Frag terms pvs types eqs theta rules) = types
getTermVars (Frag terms pvs types eqs theta rules) = map fst terms
getTheta (Frag terms pvs types eqs theta rules) = theta
getEqs (Frag terms pvs types eqs theta rules) = eqs
skolFrag (Frag _ skolvars _ _ _ _) = skolvars

showFrag message frag =
  do { (Frag xs rs tenv eqs theta rules) <- zonk frag
     ; outputString ("\n********** Frag ***************" ++ message ++
           "\nBindings = "++plistf showBind "" (take 5 xs) ", " ""++
           "\nSkolem = "++show rs++
           "\nRefinement = "++ show theta++
           "\nAssumptions = "++showPred eqs++"\n*********************") }


dispFrag message frag =
   do { (Frag xs rs tenv eqs theta rules) <- zonk frag
      ; warnM [Ds ("\n********** Frag ***************" ++ message)
                ,Ds "\n   Bindings = ",Dlf dispBind (take 5 xs) "\n              "
                ,Ds "\n     Skolem = ",Dl rs ", "
                ,Ds "\n Refinement = ",Dl theta ", "
                ,Ds "\nAssumptions = ", Dl eqs "; "
                ,Ds "\n   Theorems = ",Dl (map snd rules) "; "]}

showBind (x,(t,mod,_,_)) = show x ++":"++show t
dispBind d (x,(t,mod,_,_)) = displays d [Dd x,Ds ":",Dd t]

----------------------------------------------------------------
-- simple operations on TcEnv

levelInc :: TC a -> TC a
levelInc (Tc m) = Tc (\env -> m (env {level = (level env) + 1}))

levelDec :: TC a -> TC a
levelDec (Tc m) = Tc (\env -> m (env {level = (level env) - 1}))

newLoc :: Loc -> TC a -> TC a
newLoc loc (Tc m) = Tc (\env -> m (env {location = loc}))

getTyFuns :: TC [(String,DefTree TcTv Tau)]
getTyFuns = Tc (\ env -> return (tyfuns env,[]))

getAssumptions = Tc (\ env -> return (assumptions env,[]))

getAllTheorems = Tc (\ env -> return((concat (map snd (Map.toList (rules env)))),[]))

getLemmas :: TC[RWrule]
getLemmas = do { ts <- getAllTheorems; return(filter isLemma ts)}


getTCEnv :: TC (FiniteMap Var (Sigma,Mod,CodeLevel,Exp))
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
             case lookup x table of
                  Just (tree) -> return(k,t,show tree)
                  Nothing -> return(k,t,"")
         f (x:xs) ts = f xs ts

getVar :: Var -> TcEnv -> Maybe(Sigma,Mod,CodeLevel,Exp)
getVar nm env = Map.lookup nm (var_env env)

getRules :: String -> TcEnv -> [(RWrule)]
getRules nm env =
  case Map.lookup nm (rules env) of
    Nothing -> []
    Just ts -> ts

mknoisy env = setMode "solving" True >> return env
mksilent env = setMode "solving" False >> return env

setAssumptions :: [Pred] -> Mtc TcEnv a b -> Mtc TcEnv a b
setAssumptions d (Tc m) = Tc(\env -> m (env {assumptions = d}));

valueNames env = foldr add [] (Map.toList (var_env env))
  where add (Global nm,(sigma,mod,level,exp)) xs = nm:xs
        add _ xs = xs

typeNames env = map f (type_env env)  where f (name,tau,polykind) = name

---------------------------------------------------------
-- Printing things in the Environment

showAllVals n env = mapM f (take n (Map.toList(var_env env)))
  where f (nm,(sigma,mod,level,exp)) = outputString (show nm ++ " : " ++alpha [] sigma)

showSomeVals p env = mapM f (filter p (Map.toList(var_env env)))
  where f (nm,(sigma,mod,level,exp)) = outputString (show nm ++ " : " ++alpha [] sigma)

showVals vs = do { env <- getTCEnv
                    ; warnM [Dlf f (filter p (Map.toList env)) "\n  "]}
  where p (Global s,_) = any (==s) vs
        f d (nm,(sigma,mod,level,exp)) = displays d [Ds (show nm++" :: "),Dd sigma]

showBindings :: TyCh m => m ()
showBindings = do { bs <- getBindings; warnM [Ds "bindings = ",Dl bs ", "]}

showAssumptions :: TC()
showAssumptions = do { bs <- getAssumptions; warnM [Ds "assumptions = ",Dl bs ", "]}

completionEntry env = entry
  where tnames = typeNames env
        vnames = valueNames env
        all = nub(vnames ++ tnames)
        entry s = (filter (prefix s) all)

showSome xs =
 do { let getenv = (Tc (\ x -> return(x,[])))
          p (Global x,_) = x `elem` xs
    ; env <- getenv
    ; showSomeVals p env
    }


-- ==================================================================
-- Typability means membership in the class Typable (See RankN.hs)
--------------------------------------------------------------------
-- Literals are Typable

instance Typable (Mtc TcEnv Pred) Lit Rho where
  tc x@(Int n) expect = zap x (Rtau intT) expect
  tc x@(Char c) expect = zap x (Rtau charT) expect
  tc x@(Unit) expect = zap x (Rtau unitT) expect
  tc x@(ChrSeq s) expect = zap x (Rtau chrSeqT) expect
  tc x@(Symbol n) expect = zap x (Rtau symbolT) expect
  tc x@(Float n) expect = zap x (Rtau floatT) expect
  tc x@(Tag s) expect = zap x (Rtau (tlabel(ttag ('`':s)))) expect


----------------------------------------------------------------
-- The main workhorse which does Exp. This is modelled after the
-- function in "Practical type inference for arbitrary-rank types"
-- by Simon Peyton Jones and Mark Shields, modified to accomodate
-- "Simple Unification-based Type Inference for GADTS" by Simon
-- Peyton Jones, Stephanie Weirich, and Dimitrios Vytiniotis

instance Typable (Mtc TcEnv Pred) Exp Rho where
  tc = typeExp Wob

inferExp :: Exp -> TC(Rho,Exp)
inferExp = infer

typeExp :: Mod -> Exp -> Expected Rho -> TC Exp
typeExp mod (Lit x) expect = do { x' <- tc x expect; return (Lit x') }
typeExp mod (Var v) expectRho =
     do { m <- getLevel
        ; (sigma,mod,n,exp) <- lookupVar v
        ; when (n > m) (failD 2 [Ds (show v++" used at level "++show m++" but defined at level "++show n)])

        ; when False --(show v=="Base")
            (do { truths <- getTruths
                ; warnM [Ds ("\nChecking variable "++show v)
                        ,Ds "\nSigma = ",Dd sigma
                        ,Ds "\nExpect = ", Dd expectRho
                        ,Ds "\nTruths = ",Dl truths ", "
                        ,Ds "\nmod = ",Dd mod]
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

        ; whenM(show fun == "half")
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
     do { loc <- getLoc
        ; (ann_ty,_) <- checkPT loc pt
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

        --; (e2,mod2) <- scrApp (exp,dom)
        --; dom2 <- zonk dom

        ; ms2 <- checkL (modAnd mod mod2) ms (Check (arrow (simpleSigma dom2) rng))
        ; return(Case e2 ms2) }
typeExp mod (Case exp ms) (Infer ref) =
     do { rng <- newRho star
        ; (dom,e2) <- infer exp
        ; ms2 <- checkL mod ms (Check (arrow dom rng))
        ; writeRef ref rng

        -- ; rng <- newTau star
        -- ; dom <- newTau star
        -- ; (e2,mod) <- scrApp (exp,dom)
        -- ; d2 <- zonk dom
        -- ; ms2 <- checkL mod ms (Check (Rtau (tarr dom rng)))
        -- ; writeRef ref (Rtau rng)

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
        ; rules <- getAllTheorems

        ; typ <- zonk expect
        ; warnM [Ds ("\n\n*** Checking: " ++ (take 62 (show e)))
                ,Ds "\n*** expected type: ",Dd typ
                ,Ds "\n***    refinement: ",Dd truths
                ,Ds "\n***   assumptions: ",Dl ass2 ", "
                ,Ds "\n***      theorems: ",Dl (filter (not . axiom) rules) "\n                   "]
        ; env <- tcEnv
        ; checkLoop typ env
        ; x <- typeExp mod e expect
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

--------------------------------------------------------------------
-- Functions to report reasonably readable  errors

notfun e fun_ty s =
   failK "notfun" 2 [Ds "\nIn the expression: "
                ,Dd e
                ,Ds "\nthe function has a non-functional type: "
                ,Dd fun_ty]

badarg e arg_ty s =
 do { z <- zonk arg_ty
    ; failK "badarg" 2
       [Ds "\nIn the expression: "
       ,Dd e
       ,Ds "\nthe argument did not have type: "
       ,Dn arg_ty
       ,Ds s]}

resulterr e res_ty expect s =
  do { ex <- case expect of {Check t -> return t; Infer ref -> readRef ref }
     ; rt <- zonk res_ty
     ; ex2 <- zonk ex
     ; refinement <- getBindings
     ; failK "resulterr" 2
         [Ds "\nIn the expression: "
         ,Dn e
         ,Ds "the result type: "
         ,Dn rt
         ,Ds "was not what was expected: "
         ,Dn ex
         ,Ds "refinement: ",Dl refinement ", "
         ,Ds ("\n"++s)
         -- ,Ds ("\n"++(shtt rt)++" =/= "++shtt ex)
         ]}

morePoly::(Show a,Exhibit (DispInfo Z) a,Exhibit (DispInfo Z) b
          ,Exhibit (DispInfo Z) c,Subsumption m b(Expected c)
          ,TypeLike m b,TypeLike m c)
          => a -> b -> Expected c -> m ()

morePoly exp sigma expect =
   handleM 2 (morepoly (show exp) sigma expect) (resulterr exp sigma expect)

-- ===============================================================================
-- testing morepoly
-- t1 :: IO [()]
-- t1 = mapM (uncurry test) subpairs

test :: String -> String -> IO ()
test s1 s2 = runTC tcEnv0
  ((case (parsePT s1,parsePT s2) of
    (a@(Forallx All xs _ x),b@(Forallx All ys _ y)) ->
        do { (t1,_) <- checkPT Z a
           ; (t2,_) <- checkPT Z b
           ; b <- morepoly "test" t1 t2; outputString (show b ++ "\n") }
    (a@(Forallx All xs _ x),y) ->
        do { (t1,_) <- checkPT Z a
           ; t2 <- toRho typeConstrEnv0 y
           ; b <- morepoly "test"  t1 t2; outputString (show b ++ "\n") }
    (x,y) ->
        do { t1 <- toRho typeConstrEnv0 x
           ; t2 <- toRho typeConstrEnv0 y
           ; b <- morepoly "test"  t1 t2; outputString (show b ++ "\n") }) :: TC ())

--------------------------------------------------------------
-- fun Matches are Typeable  (Match [Pat] Exp Dec)
-- This instance useable for (Fun matches)
-- f :: d1 -> d2 -> rng
-- f p1 p2 = e    leads to a call like:
-- tc (line 1, [p1,p2],Normal e,[]) (Check (d1 -> d2 -> rng))

instance Typable (Mtc TcEnv Pred) (String,Loc,[Pat],Body Exp,[Dec]) Rho where
  tc = typeMatchPs Wob

typeMatchPs:: Mod -> (String,Loc,[Pat],Body Exp,[Dec]) -> Expected Rho -> TC(String,Loc,[Pat],Body Exp,[Dec])
typeMatchPs mod (x@(nm,loc,ps,Unreachable,ds)) (Check t) = newLoc loc $
      do { let good message = return x
               bad = failD 3 [Ds "The patterns: ",Dl ps ", ",Ds "  do not guard unreachable code."]
         ; truths <- collectEqAssump
         ; handleK (=="bad refinement") 4 (checkBndrs True Rig nullFrag ps t >> bad) good }
typeMatchPs mod (nm,loc,ps,body,ds) (Check t) = newLoc loc $
     do { (frag1,ps1,rng) <- checkBndrs localRename mod nullFrag ps t
        ; t11 <- zonk t
        ; let err s  =
               (do { (Frag zs _ _ ts theta rs) <- zonk frag1
                   ; truths <- getBindings
                   ; failK "tcMatch[Pat]" 3
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
                                      (chBody1 mod frag1 body rng2)))
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

collectEqAssump =
 do { truths <- getAssume
    ; let separate (EqAssump x y) ans = (x,y):ans
          separate x ans = ans
    ; return(foldr separate [] truths)}

matchContext ps body = bodyName (Pvar (Global ("match: "++show ps))) body

-- Contexts are passed as the 1st argument to "underLet" and "underLam". They
-- are a String and are used in error messages. We compute legible ones here.

mContxt loc nm ps body =
    "\n"++show loc++"\n"++nm++plist " " ps " " " = "++ lhs ++ dots
  where bodyString = (show body)
        lhs = take 20 bodyString
        dots = if length bodyString > 20 then " ... " else " "
wContxt loc nm ps =
  "\n"++show loc++"\n"++nm++plist " " ps " " " = ... where ds"

chBody1 mod frag body rng =
  do { let verbose = False
           vs = (getTermVars frag)
           xs = skolFrag frag
     ; when verbose
        (do { warnM [Ds ("\n*****************\nChecking clause: "++show body)
                    ,Ds ("\nhas the type:    "),Dd rng
                    ,Ds "\nIn the scope of vars:"
                    ,Ds "\nskolem vars: ",Dl xs ", "
                    ,Ds "\nmode = ",Dd mod]
            ; showVals (map show vs)
            ; showBindings
            ; showAssumptions
            ; return()})
     ; (ans,ps) <- peek (typeBody mod body (Check rng))
     ; rng2 <- zonk rng
     ; whenM verbose [Ds "The preds generated = ",Dl ps "; "
                     ,Ds "\nThe range type computed ",Dd rng2]
     ; return ans
     }

peek :: TC a -> TC (a,[Pred])
peek x = do { (a,eqs) <- collectPred x; injectA " peek " eqs; return(a,eqs) }

--------------------------------------------------------------------------
-- Bodys are Typable

instance Typable (Mtc TcEnv Pred) (Body Exp) Rho where
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

-----------------------------------------------------------
-- (Case matches) are Typeable

-- case e of { (C p1 p2) -> e }    leads to a call like
-- tc (line 1,(C p1 p2),Normal e,[]) expected

instance Typable (Mtc TcEnv Pred) (Match Pat Exp Dec) Rho where
  tc = typeMatch Wob

typeMatch:: Mod -> Match Pat Exp Dec -> Expected Rho -> TC (Match Pat Exp Dec)
typeMatch mod (x@(loc,p,Unreachable,ds)) (Check t) =
      do { (dom,rng) <- unifyFun t
         ; let good message = return x
               bad = failD 3 [Ds "The pattern: ",Dd p,Ds " does not guard unreachable code."]
               sigmaRho (Forall l) = rho  where (vs,(ps,rho)) = unsafeUnwind l
               action = do { (frag,p1) <- checkBndr True Rig nullFrag dom p
                           ; fragMGU ("Unreachable",sigmaRho dom) frag}
         ; handleK (=="bad refinement") 3 (action >> bad) good }
typeMatch mod (loc,p,body,ds) (Check t) = newLoc loc $
     do { (dom,rng) <- (unifyFun t)
        ; (frag1,p1) <- checkBndr localRename mod nullFrag dom p
        ; range <- applyTheta mod frag1 rng
        ; frag99 <- zonk frag1
        ; let err s  =
               (do { (Frag zs _ _ truths theta rs) <- zonk frag1
                   ; binds <- getBindings
                   ; failK "tcMatchPat" 2
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
                             (typeBody mod body (Check range)))) err
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

--------------------------------------------------------------------
-- Patterns are Typeable
-- Usually we want Pat in the class TypeableBinder. But, for 1st class
-- patterns we need both. E.g. a delc like:    pattern LHS = RHS
-- pattern If x y z = Case x [(True,y),(False z)]
-- where we need to check that the pattern on the RHS is well formed
-- when using the variables defined on the LHS.

instance Typable (Mtc TcEnv Pred) Pat Rho where
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


checkL mod [] expect = return []
checkL mod (t:ts) expect =
   do { t2 <- typeMatch mod t expect
      ; ts2 <- checkL mod ts expect
      ; return(t2:ts2) }

--------------------------------------------------------------------
-- Stmts are Typable

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


-- ===============================================================
-- A class of data structures that are binding instances

class TypableBinder term where
  checkBndr :: Bool -> Mod -> Frag -> Sigma -> term -> TC(Frag,term)
  inferBndr :: Bool -> Frag -> term -> TC(Sigma,Frag,term)

--  The most common patterns of useage

inferBndrs :: Bool -> Frag -> [Pat] -> TC([Sigma],Frag,[Pat])
inferBndrs rename k [] = return([],k,[])
inferBndrs rename k (p:ps) =
  do { (sig,k2,p2) <- inferBndr rename k p
     ; (sigs,k3,ps2) <- inferBndrs rename k2 ps
     ; return(sig:sigs,k3,p2:ps2)}

-- checkBndrs rename mod frag [p1,p2,p3] (t1 -> t2 -> t3 -> result)
-- checkThat:  theta <- check[p1:t1, p2:t2, p3:t3], and return theta(result)

checkBndrs :: Bool -> Mod -> Frag -> [Pat] -> Rho -> TC(Frag,[Pat],Rho)
checkBndrs rename mod f0 [] result =
  do { ty <- applyTheta Wob f0 result; return(f0,[],ty) }
checkBndrs rename mod f0 (p:ps) rho =
  do { (dom,rng) <- unifyFun rho
     ; (f1,p1) <- checkPat rename mod f0 dom p
     ; rng2 <- applyTheta Wob f1 rng
     ; (f2,ps2,rng3) <- checkBndrs rename mod f1 ps rng2
     ; return(f2,p1:ps2,rng3)
     }

-------------------------------------------------------
-- Var is a TypableBinder

instance TypableBinder Var where
  checkBndr rename mod k t var =
     do { level <- getLevel
        ; v <- alphaN rename var
        ; ans <- addTermVar (var,(t,Rig,level,Var v)) k
        ; return(ans,v) }
  inferBndr rename k var =
     do { sigma <- newSigma star;
        ; level <- getLevel
        ; v <- alphaN rename var
        ; ans <- addTermVar (var,(sigma,Wob,level,Var v)) k
        ; return(sigma,ans,v) }

alphaN :: Fresh m => Bool -> Var -> m Var
alphaN True (Global s)  = do { nm <- fresh; return(Alpha s nm)}
alphaN True (Alpha s _) = do { nm <- fresh; return(Alpha s nm)}
alphaN False name = return name

---------------------------------------------------------------
-- A Pat is a TypeableBinder

instance TypableBinder Pat where
  checkBndr = checkPat
  inferBndr = inferPat

inferPat :: Bool -> Frag -> Pat -> TC(Sigma,Frag,Pat)
inferPat rename k pat =
  do { sigma <- newSigma star
     ; (k2,p2) <- checkPat rename Wob k sigma pat
     ; sigma2 <- zonk sigma
     ; return (sigma2,k2,p2)}


checkPat :: Bool -> Mod -> Frag -> Sigma -> Pat -> TC(Frag,Pat)
checkPat rename mod k t pat =
  case (pat,mod) of
    (Plit x,_) -> handleM 2
       (do { expect <- applyTheta mod k t
           ; p <- check x expect
           ; return(k,Plit p)}) (badRefine2 pat (getTheta k) t)
    (Pvar var,_) ->
       do { level <- getLevel
          ; v <- alphaN rename var
          ; ans <- addTermVar (var,(t,mod,level,Var v)) k
          ; return(ans,Pvar v)}
    (Pcon c ps,Wob) ->
       do { (sigma@(Forall l),mod,n,exp) <- lookupVar c
          ; (vs,assump,rho) <- existsInstance (show pat) sigma
          ; (pairs,range) <- constrRange c ps rho []
          ; (_,emittedAssump) <- collectPred (morepolySigmaRho "wobbly constr pattern" t (Rtau range))
          ; (bc,_) <- get_tvs range
          ; let hash xs ys = if null(intersect xs ys) then Rig else Wob
                -- if type vars are all existential (don't appear in range)
                -- then Mod is Rigid else its Wobbly
                addMod (pat,ty) =
                   do { (vs,_) <- get_tvs ty; return(pat,ty,hash vs bc)}
          ; triples <- mapM addMod pairs
          ; (k2,ps2) <- checkPats rename k triples
          ; let k3 = addPVS (vs \\ bc) (addEqs (assump++emittedAssump) k2)
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
                  ; let k3 = addEqs (truths ++ subPred psi assump) k2
                  ; (k4,ps2) <- checkPats rename k3 (map addRigid pairs)
                  ; return(k4,Pcon c ps2)}
          }
    (Pprod x y,mod) ->
       do { pair <- applyTheta mod k t
          ; ((t1,t2),truths) <- collectPred (sigmaPair pair)
          ; (k2,x2) <- checkPat rename mod k t1 x
          ; (k3,y2) <- checkPat rename mod k2 t2 y
          ; let k4 = addEqs truths k3
          ; return(k4,Pprod x2 y2)}
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
          ; k2 <- addTermVar (var,(t,Rig,level,Var v)) k1
          ; return(k2,Paspat v p1)}
    (Pwild,_) -> return(k,Pwild)
    (Pann p ty,_) ->
       do { scopedEnv <- extendToEnv k
          ; loc <- getLoc
          ; (sigma,_) <- inEnv scopedEnv (checkPT loc ty)
          ; eitherInfo <- morepolySS [] t sigma
          ; case eitherInfo of
             Right(s,x,y) -> failD 2 [Ds "Annotation not polymorphic enough.\n"
                                     ,Ds s,Dd x,Dd y]
             Left(psi,truths) ->
               do { (k2,p') <- checkPat rename Rig k sigma p
                  ; k3 <- addUnifier psi k2
                  ; let k4 = addEqs truths k3
                  ; return(k4,Pann p' ty)}}


ifEqualPredThenAddAssump t frag =
  do { tau <- zonk t
     ; case tau of
        (TyApp (TyApp (TyCon lev "Equal" k) x) y) ->
                 return(addEqs [(EqAssump x y)] frag)
        other -> return frag
     }

-- functions to make reasonable error reporting

badRefine pat t s x y =
  failK "bad refinement" 2
          [Ds "\nWhile infering the type of the pattern: ",Dd pat
          ,Ds "\nwe expected it to have type: ",Dd t
          ,Ds "\nbut, the current refinement fails because ",Dd x,Ds " != ",Dd y
          ,Ds ".\nSometimes reordering the patterns can fix this."]

badRefine2 pat theta t s =
  failK "bad refinement" 2
   [Ds "The current refinement: ",Dd theta,Ds "\nwon't type the pattern: "
   ,Dd pat,Ds " with type: ",Dd t
   ,Ds ".\nSometimes, when the type of one pattern depends on another,\nreordering the patterns might fix this.",Ds ("\n"++s)]


nonRigidExists z =
  [Ds "Exists patterns cannot have their type inferred:\n  "
  ,Dd z,Ds " Use a prototype signature with 'exists t . type[t]' "]

-- helper functions

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

checkPats rename k [] = return(k,[])
checkPats rename k ((p,sig,mod):xs) =
  do { (k2,p2) <- checkPat rename mod k sig p
     ; (k3,ps2) <- checkPats rename k2 xs
     ; return(k3,p2:ps2)}

---------------------------------------------------------------
-- A [Dec] is a TypableBinder
-- We assume the [Dec] has already been patitioned into
-- small mutually recursive lists. This is done by "inferBndrForDecs"


instance TypableBinder [Dec] where
  inferBndr renm k [] = return(simpleSigma unitT,k,[])
  inferBndr renm k [(AddTheorem loc xs)] =
    do { theorems <- newLoc loc (computeTheorems xs)
       ; return(simpleSigma unitT,addRules theorems k,[])  -- erase theorems
       }
  inferBndr renm frag1 ds | all isValFunPat ds =
    do { let decs = useTypeSig ds
       ; (frag2,triples) <- getDecTyp renm decs -- Step 1
       ; frag3 <-  frag2 +++ frag1
       ; ds2 <- mapM (checkDec frag3) triples   -- Step 2
       ; frag4 <- genFrag frag3
       ; return(simpleSigma unitT,frag4,ds2)
       }
  inferBndr rename frag ds = failD 2 [Ds "\nMixup in Decs\n", Ds (show ds)]
  checkBndr rename mod k sigma ds = error "Can't checkBndr a [Dec]"

-- Step 1. Compute just the "frag" for the decls. Don't check the decl bodies yet.

getDecTyp :: Bool -> [Dec] -> TC (Frag,[(Mod,Rho,Dec,[Pred],[TcTv])])
getDecTyp rename [] = return(nullFrag,[])
getDecTyp rename (d:ds) =
  do { (frag1,mod,rho,d,eqns,skols) <- frag4OneDeclsNames rename d
     ; (frag2,triples) <- getDecTyp rename ds  -- do the rest of the list
     ; frag3 <- frag2 +++ frag1
     ; return(frag3,(mod,rho,d,eqns,skols):triples) }

-- Step 2. Check the bodies. All names bound in the mutually recursive
-- set of decls are already in the frag passed as input (See Step 1).

checkDec :: Frag -> (Mod,Rho,Dec,[Pred],[TcTv]) -> TC Dec
checkDec frag (mod,_,Prim loc nm t,eqns,skols) = newLoc loc $ return(Prim loc nm t)
checkDec frag (mod,rho,Fun loc nm hint ms,eqns,skols) | unequalArities ms =
  failD 3 [Ds ("\n\nThe equations for function: "++show nm++", give different aritites.")]
checkDec frag (mod,rho,Fun loc nm hint ms,eqns,skols) = newLoc loc $
  do { frag3 <- addPred eqns frag
     ; let hasRho (loc,ps,bod,ds) =
             case rho of
               Rtau(tau @(TcTv _)) ->
                   do { ref <- newRef (error "no rho yet")
                      ; ans <- typeMatchPs mod (show nm,loc,ps,bod,ds) (Infer ref)
                      ; Rtau v <- readRef ref
                      ; unify tau v
                      ; return ans}
               other -> typeMatchPs mod (show nm,loc,ps,bod,ds) (Check rho)
           stripName (nm,loc,ps,bod,ds) = (loc,ps,bod,ds)
     ; ((assump,ms2),oblig) <-
           collectPred
           (underLamGetPred frag3 (show nm,rho) (mapM hasRho ms))
     ; solveDecObligations (show nm) rho assump oblig
     ; return(Fun loc nm hint (map stripName ms2)) }
checkDec frag (mod,rho,Val loc pat body ds,eqns,skols) = newLoc loc $
  do { let lhsString = bodyName pat body
     ; (frag2,ds2) <- inferBndrForDecs localRename ds
     ; frag3 <- addPred eqns frag
     ; ((assump,body2),oblig) <-
           collectPred
           (underLetGetPred (lhsString,rho) (addSkol skols frag3)
           (lambdaExtend frag2 (typeBody mod body (Check rho))))
     ; solveDecObligations lhsString rho assump oblig
     ; return(Val loc pat body2 ds2) }
checkDec frag (mod,rho,Pat loc nm vs p,eqns,skols) = newLoc loc $
  do { frag3 <- addPred eqns frag
     ; (Forall (Nil (assump,ty)),(Frag xs tvs tenv eqs theta rs),p2)
               <- lambdaExtend frag3 (inferBndr False nullFrag p)
     ; argtys <- compareL vs xs
     ; morepoly (show nm) (foldr arrow ty argtys) rho
     ; return(Pat loc nm vs p)}
checkDec frag (mod,rho,Reject s ds,eqns,skols) =
   handleM 7 (do { ((frag2,ds2),cs) <- collectPred (inferBndrForDecs localRename ds)
                 ; when (not(null cs)) (failD 6 [Ds "Unresolved constraints"])
                 ; failD 8 [Ds ("\nReject test: '"++s++"' did not fail.")]}) errF
       -- Its is important the the inner fail have higher failure level (8) than
       -- the outer catching mechanism (7). Because if the decl doesn't fail we want to know.
 where errF n = do { outputString ("\n*** Negative test '"++ s ++ "' fails as expected.\n")
                   ; return (TypeSig Z (Global "##test") tunit')}
checkDec frag (mod,rho,t,eqns,skols) = failD 2 [Ds "Illegal dec in value binding group: ", Ds (show t)]

----------------------------------------------------------
-- helper functions

unequalArities ms = not(same(map arity ms))
  where arity (loc,ps,body,ds) = length ps
        same [] = True
        same [x] = True
        same (x:y:zs) | x==y = same (y:zs)
        same _ = False

badOblig oblig oblig2 pat assump truths =
  do { r <- refutable oblig2
     ; failD 3 [Ds "\nWhile type checking: ", Dd pat
                     ,Ds "\nUnder the truths: "
                     ,Dl (assump++truths) ", "
                     ,Ds "\nWe tried to solve: "
                     ,Dl oblig ","
                     ,Ds "\nBut we were left with: "
                     ,Dl oblig2 ", ",r]}

solveDecObligations nm rho assump oblig =
 do { truths <- getAssume
     --; warn [Ds "\nGetting ready to solve for ",Ds (show nm),Ds "\n"]
    ; oblig2 <- solveConstraints (nm,rho) (assump++truths) oblig
    ; when (not (null oblig2)) (badOblig oblig oblig2 nm assump truths)}


refute [] term = return True
refute ((r@(RW nm key Rewrite _ _ _ _)):rs) term = refute rs term
refute ((r@(RW nm key BackChain _ _ _ _)):rs) term = refute rs term
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

predNameFromTau s (TyApp f y) = predNameFromTau s f
predNameFromTau s (TyCon l nm k) = return nm
predNameFromTau s x = failD 2 [Ds "\nNon Type constructor: "
                       ,Dd x
                       ,Ds " used as Prop in:\n  "
                       ,Dd s]

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

-- ====================================================================
-- Types in syntax are stored as PT, we need to translate them
-- into Sigma types, and check that their well formed with Kind *
-- PT types stored in Data Decs are handled differently because they
-- may have kinds other than *, and they are not always generalized.
-- We return a Sigma type, and a Fresh Rho type, and update the Display so it maps
-- the Vars in the fresh Rho to the Strings in the PT


checkPT :: Loc -> PT -> TC(Sigma,(Rho,[Pred],[TcTv]))
checkPT loc pt =
  do { tenv <- getTypeEnv
     ; (free,pt2) <- splitPT tenv pt  -- Make sure its an explicit Forallx form
     ; freeEnv <- mapM genFresh free  -- Make temp Types for translating free typevars
     ; (s@(Forall xs),snMap) <- toSigma (freeEnv ++ tenv) pt2 -- translate
     ; handleM 2 (check s (Star LvZero)) err             -- check the translation has kind *0
     ; let (names,(eqns,rho)) = unsafeUnwind xs          -- unwind to make a fresh Rho instance
     ; (nameMap,skol) <- rigid snMap names []            -- build the mappings
     ; rho2 <- sub (nameMap,[],[],[]) rho                -- make fresh Rho
     ; eqn2 <- sub (nameMap,[],[],[]) eqns               -- and fresh equations
     ; return (s,(rho2,eqn2,skol))}
 where  genFresh nm =
          do { kind <- newKind star1; var <- newFlexiTyVar kind
             ; return(nm,TcTv var,poly kind)}
        rigid ((s,nm):xs) ((nm2,k,q):ys) subst =
            do { k2 <- sub (subst,[],[],[]) k   -- in explicit foralls, earlier may bind
               ; v <- newRigidTyVar q loc s k2  -- later, so we need to apply subst to k
               ; (subst2,skols) <- rigid xs ys ((nm,TcTv v):subst)
               ; newname <- registerDisp s v    -- Update the Display to map the ridgid to the PT name
               ; return(subst2,v:skols)}
        rigid _ _ subst = return(subst,[])
        err s = failD 2 [Ds "The prototype:  ",Dd pt,Ds "\ndoes not have kind *0, because ",Ds s]

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
       g nm = (nm,AnyTyp,All)

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

inferPolyPT :: ToEnv -> PT -> TC(Sigma,Tau,PolyKind,[(String,Name)])
inferPolyPT argEnv pt =
  do { tenv <- getTypeEnv
     ; (s,names) <- toSigma (argEnv ++ tenv) pt
     ; (k::Tau,ty) <- infer s
     ; return(ty,k,poly(MK k),names)
     }

-- ===============================================================
-- data Decs
-------------------------------------------------------------------
-- Checking that a data Dec is legal requires kind checking. If the data
-- Dec is parameterized we need to compute kinds for the parameters to
-- compute a kind for the Type Constructor. This depends on the syntax used
-- 1) infer types        data T x y = C (x y)
-- 2) user annotations   data T (x :: *0 ~> *0 ) (y :: *0 ) = C (x y)
-- 3) use signtaure      T :: (*0 ~> *0 ) ~> *0 ~> *0
--                       data T x y = C (x y)
-- 4) explicit GADT      data T:: ( *0 ~> *0 ) ~> *0 ~> *0 where C:: (x y) -> T x y
-- Once the parameters are processed, we use this information to
-- compute a kind for the type constructor (i.e. T above). Below
-- we assume that user annotations (as in 2) above have been pushed into
-- the (Just kind) field of a Data decl.

kindOfTyConFromDec (GADT loc isP (Global name) k cs) =
  return(isP,name,k,univLevelFromPTkind k,loc)
kindOfTyConFromDec (Data loc isP _ (Global name) (Just k) vs cs derivs) =
  return(isP,name,k,univLevelFromPTkind k,loc)
kindOfTyConFromDec (Data loc isP level (Global name) Nothing vs cs derivs) =
  do {(argBinds,rng) <- newLoc loc (useSigToKindArgs level vs Nothing)
     ; let tkindbody = foldr Karrow' rng (map (\(nm,pt,q)->pt) argBinds)
     ; return(isP,name,tkindbody,level,loc)}

-- Given T :: a ~> b ~> * ; data T x y = ... OR data T (x:a) (y:b) = ...
-- Bind the args to their kinds [(x,a),(y,b)]. If there is No kind
-- information, use default rules, which depend on the strata information
-- which must be either type or kind, since the explicit GADT form must
-- be used for other levels.

useSigToKindArgs:: Strata -> [(Var,PT)]-> Maybe PT -> TC([(String,PT,Quant)],PT)
useSigToKindArgs strata args sig = walk args sig where
  walk [] Nothing = return ([],Star' strata)     -- implicit (T a b):: *
  walk [] (Just (Star' n))= return ([],Star' n)  -- explicit (T a b):: *
  walk [] (Just t) = failD 2 [Ds "Explict kinding for new type must result in kind *n, not ",Dd t]

  walk zs (Just (Forallx _ ps _ z)) =                 -- Signature is an explicit Forall
    do { (qs,t) <- walk zs (Just z)
       ; return(ps ++ qs,t) }

  walk ((Global v,AnyTyp):vs) Nothing =               -- Signature is missing
    do { (xs,rng) <- walk vs Nothing
       ; return((v,AnyTyp,All):xs,rng) }
  walk ((Global v,d):vs) Nothing =
    do { (xs,rng) <- walk vs Nothing
       ; return((v,d,All):xs,rng) }

  walk ((Global v,AnyTyp ):vs) (Just(Karrow' d r)) =  -- Signature is implicit Forall
    do { (xs,rng) <- walk vs (Just r)
       ; return((v,d,All):xs,rng) }
  walk ((Global v,d1):vs) (Just (Karrow' d2 r)) =
    do { (xs,rng) <- walk vs (Just r)
       -- Prefer the explicit signature, Warn the user to remove the explicit kindings.
       ; loc <- getLoc
       ; warnM [Ds ("\nNear "++show loc)
               ,Ds "\nData decl has explicit signature and explicit kindings on arguments."
               ,Ds "\nThe explicit kindings are deprecated, and should be removed."]
       ; return((v,d2,All):xs,rng)}

  walk (v:vs) (Just t) = failD 2 [Ds "Expecting kind arrow like (a ~> b), found: ",Dd t]



----------------------------------------------------------------------------
-- Compute information for each type constructor, and each constructor function.
-- in a mutually recursive set of data decls. Proceeds in several steps.
-- 1) Compute kind schemas for all of the TyCons, and a univ level for each TyCon
-- 2) Then under these schemas, check that each ConstrFun's type is classified by (Star level)
-- E.g.  data T:: *0 ~> Nat ~> *0 where
--         C:: a -> Int -> T a Z
-- schema T::*0 ~> Nat ~> *0  with level *0, then check that (a -> Int -> T a Z) :: *0
-- Then add theorems and rules, and build a Frag to return.

checkDataDecs :: [Dec] -> TC (Sigma,Frag,[Dec])
checkDataDecs decls =
  do { ds <- transDataToGadt decls
     ; (env2,tyConMap) <- kindsEnvForDataBindingGroup ds       -- Step 1
     ; css <- mapM (constrType env2) ds                        -- Step 2
     ; tyConMap2 <- mapM genTyCon tyConMap   -- After checking ConFuns, zonk and generalize TyCons
     ; conFunMap2 <- genConstrFunFrag tyConMap2 (concat css)   -- Zonk and Generalize TyFuns
     ; let lift [] types values = (types,values)
           lift ((level,isProp,(Global s,(sig,mod,n,exp))):xs) types values =
             if level >= kindStrata  -- I.e. a Kind or above, the ConFuns are types not values!
                then lift xs ((s,TyCon (lv level) s (K sig),K sig):types) values
                else lift xs types ((Global s,(sig,mod,n,exp)):values)
     ; (types,values) <- return(lift conFunMap2 tyConMap2 [])
     ; let makeRule (level,False,(Global c,(sigma,mod,_,_))) = return []
           makeRule (level,True,(Global c,(sigma,mod,_,_))) =
             sigmaToRule (Just (Axiom)) (c,sigma)
     ; rules <- mapM makeRule conFunMap2
     ; return(simpleSigma unitT,Frag values [] types [] [] (concat rules),ds)
     }

genConstrFunFrag tyConInfo conFunInfo = mapM f conFunInfo where
  tyConSub = map (\ (nm,tau,polykind) -> (nm,tau)) tyConInfo
  f (strata,isProp,(nm,(sig,mod,lev,exp))) =
    do { -- Replace TyCon's which have stale (i.e. mono) PolyKind fields
         sig1 <- sub ([],[],tyConSub,[]) sig -- TODO LEVEL
       ; sig3 <- generalize sig1  -- Now generalize
       ; return(strata,isProp,(nm,(sig3,mod,lev,exp)))}

genTyCon :: (Bool,String,Tau,PolyKind) -> TC (String,Tau,PolyKind)
genTyCon (isprop,nm,TyCon level_ _ _,K k) =
  do { k2 <- generalize k
     ; return(nm,TyCon level_ nm (K k2),K k2) }

transDataToGadt ds = mapM getGADT ds
  where getGADT (d@(GADT _ _ _ _ _)) = return d
        getGADT (x@(Data _ _ _ nm _ _ cs _)) =
           do { new <- data2gadt x
              ; if any eqConstrained cs
                   then badData nm x new
                   else return new }
        getGADT x = failD 1 [Ds (show x),Ds "\nis not a data declaration"]
        eqConstrained (Constr loc args name domains Nothing) = False
        eqConstrained (Constr loc args name domains (Just _)) = True
        badData nm x new =
           failD 2 [Ds "\n\nThe implicit form of data decls (using where clauses) has been deprecated."
                   ,Ds "\nPlease use the explicit form instead. Rather than writing:\n\n"
                   ,Ds (show x),Ds "\n\nOne should write something like:\n"
                   ,Ds ("(One may need to adjust the kind of '"++show nm++"')\n\n")
                   ,Ds (show new)]

kindsEnvForDataBindingGroup:: [Dec] -> TC(ToEnv,[(Bool,String,Tau,PolyKind)])
kindsEnvForDataBindingGroup ds =
  do { env <- getTypeEnv
     ; info <- mapM kindOfTyConFromDec ds
     ; let addTyCon (isP,name,kind,level,loc) =
            do { (sigma,_) <- toSigma env kind
               ; sigma' <- newLoc loc $
                           handleM 3 (check sigma (Star (LvSucc (lv level))))
                                     (badKind name kind)
               ; let kind = K sigma'
               ; return(isP,name,TyCon (lv (level+1)) name kind,kind)}
           delProp (isP,nm,tau,poly) = (nm,tau,poly)
     ; delta <- mapM addTyCon info
     ; return (map delProp delta ++ env, delta)
     }

-- The type environment currentMap already includes information for all the type names
-- in the mutually recursive binding group of GADTS (See kindsEnvForDataBindingGroup).
-- We are just translating the constructors to Sigma types.

constrType :: [(String,Tau,PolyKind)] -> Dec -> TC [(Int,Bool,(Var,(Sigma,Mod,CodeLevel,Exp)))]
constrType currentMap (GADT loc isProp tname tkind constrs) = (mapM each constrs) where
 each (loc,cname, vars, preds, typ) =
  do { let strata = univLevelFromPTkind tkind
     ; (_,rng) <- checkRng cname tname strata typ
     ; let bound = map (\ (nm,tau,kind) -> nm) currentMap
           rngFree = getFree [] rng \\ bound
           -- vars are Ex if they aren't in the range type
           -- E.g. 'a' in   App:: Exp (a -> b) -> Exp a -> Exp b
           -- except for *n: Eq:: forall (a:: *1) (b:: a) . Equal b b
           quant (Star' _) n = All
           quant _ n = if elem n rngFree then All else Ex
           free = getFree [] typ `union` getFreePredL [] preds
     ; sigma <-
         case vars of
           -- The constr leaves the kinding of vars implicit.  C:: T a -> T a
           [] -> do { let addQuant name = (name,AnyTyp,quant AnyTyp name)
                          args = map addQuant (free \\ bound)
                    ; (nmMap,windupList,envMap) <- argsToEnv args currentMap
                    ; rho <- toRho envMap typ
                    ; ps <- toPred envMap (Just preds)
                    ; return(Forall(windup windupList (ps,rho)))}
           -- The constr has explicit vars.  C:: forall a . T a -> T a
           _  -> do { let addQuant (name,kind) = (name,kind,quant kind name)
                          quantVars = map addQuant vars
                          sigmaPT = Forallx All quantVars preds typ
                    ; (sigma,nmMap) <- toSigma currentMap sigmaPT
                    ; return sigma}
     ; newLoc loc $
       handleM 3 (check sigma (Star (lv strata)))
                 (illFormed cname sigma (Star (lv strata)))
     ; sigma2 <- zonk sigma
     ; return(strata,isProp,(cname,(sigma2,Rig,0,Var cname)))
     }

--------------------------------------------------------------------------
-- helper and error checking functions for Data Decs

-- translate a [Pred] from a Maybe[Pred]
toPred env Nothing = return[]
toPred env (Just xs) = toEqs env xs

badKind name tau message =
  failM 3 [Ds "\nWhile checking the data declaration for: ",Ds name
          ,Ds "\nwe checked the well formedness of its kind: ",Dd tau
          ,Ds "\nAn error was found.\n",Ds message]

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

illFormed name rho kind message =
  failM 3 [Ds "\nWhile checking the type of the constructor: ",Dd name
          ,Ds "\nwe checked the well-formedness of:\n  ",Dd rho,Ds " :: ",Dd kind
          ,Ds "\nAn error was found.\n",Ds message]

-----------------------------------------------------------
-- data decls are deprecated in favor of GADTs. But we still
-- accept simple data decs at the type and kind level provided
-- they don't have any where clauses. Even if they do, we suggest
-- a translation.   data2gadt translates from:
--
-- data T a b
--   = C a (T a b)
--   | D
--
-- To:
--
-- data T:: *0 ~> *0 ~> *0 where
--   C:: forall (a:*0) (b:*0) . a -> T a b -> T a b
--   D:: forall (a:*0) (b:*0) . T a b

data2gadt (Data loc isP strat tname@(Global nm) hint args cs derivs) =
 do { (argBinds,rng) <- newLoc loc (useSigToKindArgs strat args hint)  -- ([(a:*0),(b:*0)],*0)
    ; let name (nm,kind,quant) = nm
          range = applyT' (map TyVar' (nm : map name argBinds))     -- T a b
          kind = foldr Karrow' rng (map (\(nm,pt,q)->pt) argBinds)  -- *0 ~> *0 ~> *0
          proj (name,kind,quant) = (name,kind)
          each (Constr loc targs cname doms preds) =
               let whereCls = some preds
                   (unifier,constraints) = splitWhere whereCls ([],[])
               in (loc,cname,map h targs ++ map proj argBinds
                  ,constraints
                  ,ptsub unifier (arrowUp strat doms range))
          var (Global s) = s
          var (x@(Alpha _ _)) = show x
          h (variable,k) = (var variable,k)
          some (Just xs) = xs
          some Nothing = []
    ; return(GADT loc isP tname kind (map each cs))
    }

arrowUp strata [] t = t
arrowUp 0 (x:xs) t = Rarrow' x (arrowUp 0 xs t)
arrowUp n (x:xs) t = Karrow' x (arrowUp n xs t)

splitWhere [] ans = ans
splitWhere ((Equality' (TyVar' nm) t):xs) (un,ps) = splitWhere xs ((nm,t):un,ps)
splitWhere ((Equality' t (TyVar' nm)):xs) (un,ps) = splitWhere xs ((nm,t):un,ps)
splitWhere (x:xs) (un,ps) = splitWhere xs (un,x:ps)

-- =====================================================================
-- Fun and Val Decs
------------------------------------------------------------------------

isValFunPat (Val _ _ _ _) = True
isValFunPat (Fun _ _ _ _) = True
isValFunPat (Pat _ _ _ _) = True
isValFunPat (TypeSig _ _ _) = True
isValFunPat (Reject s d) = True
isValFunPat (Prim l n t) = True
isValFunPat _ = False

-- We assume ds are all "where" or "let" declarations, such as
-- function, val, theorem decls. No "data" or "type" decls allowed.

inferBndrForDecs :: Bool -> [Dec] -> TC (Frag,[Dec])
inferBndrForDecs renam [] = return(nullFrag,[])
inferBndrForDecs renam ds =  many dss
  where (dss,pairs) = topSortR freeOfDec ds
        many [] =  return(nullFrag,[])
        many (ds:dss) =                                      -- For each mutually recrsive nest
           do { (_,frag1,xs) <- inferBndr renam nullFrag ds  -- MOST OF THE WORK DONE HERE
              ; let names = concat(map decname ds)
                    (_,message) = displays disp0 [Ds"The binding group: ",Dl names ","]
                              -- previous nests, can be seen by later nests, so use "underLet"
              ; (frag2,ys) <- underLet (message,starR) frag1 (many dss)
              ; frag3 <- frag2 +++ frag1
              ; return (frag3,xs++ys)}

-- Used in Step 1 (of inferBndr), to get a frag for the names bound in a single decl
-- In a mutually recursive nest, these Frags are all (+++) together.

frag4OneDeclsNames rename (d@(Val loc (Pann pat pt) body ds)) = newLoc loc $
  do { (sigma,(rho,assump,skol)) <- checkPT loc pt    -- use the hint to get rho and display
     ; (frag,pat2) <- checkBndr rename Rig nullFrag sigma pat
     ; return(addSkol skol frag,Rig,rho,Val loc pat2 body ds,assump,skol)}
frag4OneDeclsNames rename (Val loc pat body ds) = newLoc loc $
  do { info <- guess body
     ; case info of
        (Just t,Rig) ->
           do { -- warnM [Ds "Guessing ",Dd body,Ds ":: ",Dd t]
              ; (frag,pat2) <- checkBndr rename Rig nullFrag (simpleSigma t) pat
              ; return(frag,Rig,Rtau t,Val loc pat2 body ds,[],[])}
        (any,mod) ->
           do { (sigma,frag,pat2) <- inferBndr rename nullFrag pat
              ; (rigid,assump,rho) <- rigidTy Ex loc (show pat) sigma
              ; return(frag,mod,rho,Val loc pat2 body ds,assump,[])}
     }
frag4OneDeclsNames rename (Fun loc nm Nothing ms) = newLoc loc $
  do { sigma <- newSigma star
     ; (frag,nm2) <- checkBndr rename Wob nullFrag sigma nm
     ; (rigid,assump,rho) <- rigidTy Ex loc (show nm) sigma
     ; r1 <- zonk rho
     ; return(frag,Wob,r1,Fun loc nm2 Nothing ms,assump,[])}
frag4OneDeclsNames rename (Fun loc (nm@(Global fname)) (Just pt) ms) = newLoc loc $
  do { (sigma,(rho,assump,skol)) <- checkPT loc pt -- use the hint to get rho and display
     ; (frag,nm2) <- (checkBndr rename Rig nullFrag sigma nm)
     ; r1 <- zonk rho
     ; return(addSkol skol frag,Rig,r1,Fun loc nm2 (Just pt) ms,assump,skol)}
frag4OneDeclsNames rename (Pat loc nm vs p) = newLoc loc $
  do { (sigma,frag,nm2) <- inferBndr rename nullFrag nm
     ; (rigid,assump,rho) <- rigidTy Ex loc (show nm) sigma
     ; return(frag,Wob,rho,Pat loc nm2 vs p,assump,[])}
frag4OneDeclsNames rename (Reject s ds) = return (nullFrag,Wob,Rtau unitT,Reject s ds,[],[])
frag4OneDeclsNames rename (Prim l nm t) =
  do { (sigma,frag,_) <- inferBndr rename nullFrag (Pann (Pvar nm) t)
     ; return(frag,Wob,error "Shouldn't Check Prim type",Prim l nm t,[],[]) }
frag4OneDeclsNames rename d = failD 2 [Ds "Illegal dec in value binding group: ",Ds (show d)]


-- ===================================================================
-- Implementing Smart Application
--
-- For SCR-APP to be applicable the following MUST hold
-- 1) term must be of the form (c x1 x2 xn)  n >= 0
-- 2) c is an atom and has a rigid type
-- 3) its type is of the form:  forall as .preds => t1 -> t2 -> tn -> rng
--    Note that n must be the same in both the type and term.
-- 4) then return (c,rng,as,[(x1,Check t1),(x2,Check t2),(xn,Check tn)])

scrShape (Var c) = True
scrShape (Lit n) = True
scrShape (CheckT x) = scrShape x
scrShape (App f x) =
  case unApply f [x] of
    (Var c,xs) -> all scrShape xs
    other -> False
scrShape other = False

scrType (CheckT x) = scrType x
scrType (Lit n) =
  do { (Rtau t,_) <- infer n; return t}
scrType (Var c) =
  do { (sigma,Rig,n,exp) <- lookupVar c
     ; (preds,Rtau tau) <- instanTy sigma
     ; return tau}
scrType t@(App f x) =
  do { ftyp <- scrType f
     ; xtyp <- scrType x
     ; rng <- newTau star
     ; unify (tarr xtyp rng) ftyp
     ; return rng }
scrType x  = fail "does not have scrShape"

scrMod term | not(scrShape term) = return (Nothing,Wob)
scrMod term =
  handleM 99 (do { t <- scrType term
                 ; (t2,mod) <- rigidity t
                 ; return (Just t2,mod)})
             (\ n -> return (Nothing,Wob))

guess (Normal exp) = scrMod exp
guess _ = return (Nothing,Wob)

------------------------------------------------------------------------
-- Helper functions for typing [Dec]

-- rigidTy is called when checking the body of a Dec with an explicit
-- type signature. It replaces all type variables with kinds classified
-- by *1 (i.e. *0 or other kinds classified by *1) with
-- new rigid type variables. For example a type like
-- (forall (k:*1) (u:k) a . (AtomX u) -> a -> Pair)
-- should rigidify "u" and "a", but not "k"

rigidTy :: TyCh m => Quant -> Loc -> String -> Sigma -> m([TcTv],[Pred],Rho)
rigidTy q loc s sigma = unBindWith (newRigid loc s) sigma

bodyName pat (Normal e) = show e
bodyName pat (Guarded _) = "guarded pattern: "++show pat
bodyName pat Unreachable = "unreachable"

-- Generalize a Frag after type inference
genFrag (Frag xs ys tenv eqs theta rs ) =
     do { zs <- mapM gen xs; return(Frag zs ys tenv eqs theta rs )}
  where gen (var,(sigma@(Forall (Nil b)),mod,level,exp)) =
            do { s1 <- zonk sigma
               ; s2 <- generalize b; return (var,(s2,mod,level,exp))}
        gen (var,(sigma,mod,level,exp)) =
            do { s2 <- zonk sigma; return(var,(s2,mod,level,exp)) }

-- Compare that all the vars in a pattern Dec are used
-- This is part of the wobbly stuff.

compareL :: TyCh m => [Var] -> [(Var,(ty,Mod,CodeLevel,exp))] -> m [ty]
compareL xs fs =
    do { tys <- mapM get xs
       ; when (not ((length xs) == (length fs)))
              (failD 2 [Ds "Unknown var in pattern."])
       ; return tys }
  where get x = case lookup x fs of
                  Nothing -> failD 2 [Ds "Unused formal parameter: ",Dd x]
                  Just (ty,mod,_,_) -> return ty

-- Generate a reasonable error message when Skolem vars escape

escapes :: TyCh m =>  [(String,Sigma,[TcTv])] -> [TcTv] -> m ()
escapes trips [] = return ()
escapes trips bad = do { as <- getBindings
                       ; d0 <- readRef dispRef
                       ; (display,lines) <- foldrM (f as) (d0,"") bad
                       ; writeRef dispRef display
                       ; failK "escapes" 2 [Ds lines] }
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
        f as other (d1,str) = return(displays d1 [Ds "The type variable: ",Dd other,Ds (" escapes."++str)])
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
           (escapes [("the exp\n   "++show term,(Forall (Nil([],typ))),bad)] bad)
    }

-- ========================================================
-- When type checking under a binder, we compute a frag for the
-- binder, then type check in the scope of the binder in a new
-- environment extended by the Frag. The extension is different
-- for each kind of language feature, such as "lambda" or "let"

composeMGU :: MGU -> MGU -> MGU
composeMGU s1 s2 = ([(u,subTau s1 t) | (u,t) <- s2] ++ s1)

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


lookupVar :: Var -> TC (Sigma,Mod,CodeLevel,Exp)    -- May fail
lookupVar n = do { env <- getTCEnv
                 ; case Map.lookup n env of
                     Just(ty@(sigma,mod,n,exp)) ->
                        case mod of
                          Wob -> return ty
                          Rig -> do { theta <- getBindings
                                    ; sig2 <- sub ([],theta,[],[]) sigma
                                    ; return(sig2,mod,n,exp)}
                     Nothing -> failD 2 [Ds "Not in scope: ", Dd n]}

fragMGU :: (String,Rho) -> Frag -> TC([Pred],MGU)  -- FIX THETA
fragMGU (name,rho) (Frag _ _ _ eqs theta rs) = handleM 3 (mguM ("7."++name,rho) eqs) err
  where err mess = failK "mguErr" 2
               [Ds mess
               ,Ds "\nThe patterns: "
               ,Ds name
               ,Ds "\nmay have inconsistent types, indicating unreachable code."]

underLet :: (String,Rho) -> Frag -> TC a -> TC a
underLet s frag x = do { (_,ans) <- underLetGetPred s frag x; return ans}

underLam :: Frag -> (String,Rho) -> TC a -> TC a
underLam frag p x = do { (_,ans) <- underLamGetPred frag p x; return ans}

-- Like underLet and underLam, but extract the predicates generated

underLamGetPred :: Frag -> (String,Rho) -> TC a -> TC([Pred], a)
underLamGetPred frag p@(nm,rho) x =
   do { frag2 <- zonk frag
      ; (ans,preds) <- extractAccum (under (lambdaExtend) p frag2 x)
      ; return(preds,ans) }

underLetGetPred :: (String,Rho) -> Frag -> TC a -> TC([Pred],a)
underLetGetPred s@(nm,rho) frag x =
  do { --(preds,unifier) <- fragMGU s frag;
       (ans,preds) <- extractAccum (under letExtend s frag x)
     ; return(preds,ans)
     }

---------------------------------------------------------------
-- all the work is done here

-- HERE ###  -- FIX THETA
under :: (Frag -> b -> TC c) -> (String,Rho) -> Frag -> b -> TC c
under extend (p@(nm,rho)) frag comp =
  do { frag2@(Frag xs patVars tenv eqs theta rs) <- zonk frag
     -- This is where everything happens, the rest of the code
     -- just deals with the consequences.
     -- ; dispFrag nm frag
     ; (answer,collected) <- handleM 3 (collectPred(extend frag2 comp))
                                       (underErr1 patVars)
     ; let pf (Equality _ _) = True
           pf (EqAssump _ _) = True
           pf _ = False
           (oblig,residual) = partition pf collected
     ; assump <- getTruths  -- Truths we already know, "eqs" are truths we will add
     ; un <- getBindings
     ; theta2 <- zonk theta
     ; eqs2 <- zonk eqs
     ; whenM False [Ds "\nTheta = ",Dl (theta2 ++ un) ", "
                   ,Ds "\nTruths = ",Dl (eqs2 ++ assump) "; "
                   ,Ds "\nObligations = ", Dl oblig "; "]
     -- First try and discharge the obligations incurred

     ; steps <- getBound "narrow" 25
     ; unifier <- handleM 1
                  (solveByNarrowing (3,steps) ("9."++nm,rho)
                                    (eqs2 ++ assump) (foldr pred2Pair [] oblig))
                  (underErr frag nm assump oblig)
     ; u2 <- zonk unifier

     -- The unifier obtained by solving the obligations must be
     -- consistent with the bindings in the Type Checking Env.
     -- These come either from a prototype, or a GADT constructor.
     -- If they're not consistent then the function less
     -- general then the user declared.

     ; let acc (Equality (TcTv x) tau) ans = (x,tau):ans
           acc (Equality tau (TcTv x)) ans = (x,tau):ans
           acc x ans = ans
     ; whenM False
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


     ; d1 <- whenM False
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
     ; when (not (null bad)) (escapes triples bad)
     ; injectA (" under "++nm++" ") passOn
     ; return answer
     }


-----------------------------------------------------------------
-- helper functions

pred2Pair (Equality x y) ans = (x,y):ans
pred2Pair (EqAssump x y) ans = (x,y):ans
pred2Pair (Rel t) ans = ans

underErr1 patvars message =
    do { (d1@(DI (pairs,bad,supply))) <- readRef dispRef
       ; failK "underErr1" 3 [Ds (newmessage pairs)]}
  where bad pairs = concat [ match dispv patv | dispv <- pairs, patv <- patvars]
        --match (m,freshname) (Tv n (Rigid Ex loc s) k) | m==n = [(freshname,loc,s)]
        match (ZTv (Tv m flav k),freshname) (Tv n (Rigid Ex loc s) k2)
              | m==n = [(freshname,loc,s)]
        match _ _ = []
        newmessage pairs = message ++ concat(map report (bad pairs))
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

underErr frag pat assump oblig s =
   -- showFrag "UnderErr" frag >>
   failK "underErr" 2
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

-- ===============================================================================
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

-- ======================================================================
-- Code for doing kind inference and evaluating type functions like
-- plus :: (Nat ~> Nat ~> Nat)
-- {plus (S x) y} = S {plus x y}
-- {plus Z y} = y

computeTypeFunEnv :: TcEnv -> [Dec] -> TC TcEnv
computeTypeFunEnv env xs =
  do { triples <- mapM doOneTypeFun xs
     ; return (env{ type_env = triples ++ type_env env })}
 where doOneTypeFun (t@(TypeFun loc nm Nothing ms)) =
         fail ("\nType functions must be explicitly kinded with kind signature\n"++show t)
       doOneTypeFun (TypeFun loc nm (Just pt) ms) =
          do { (nmSigmaType,monoKindAsTau,nmTypeKind,names) <- inferPolyPT [] pt
             ; let poly = K(nmSigmaType)
                   getLevel (Star n) = n
                   getLevel _ = lv 1
             ; return (nm,TyCon (getLevel monoKindAsTau) nm poly,poly) }

hasMonoTypeFun :: TcEnv -> [Dec] -> TC [(String,DefTree TcTv Tau)]
hasMonoTypeFun env [] = return []
hasMonoTypeFun env1 (dd@(TypeFun loc nm (Just pt) ms) : more) =
  do { (nmSigmaType,monoKind,nmTypeKind,names) <- inferPolyPT [] pt
     ; let polyt@(K(sigma)) = K(nmSigmaType)
     ; clauses <- mapM (checkLhsMatch (type_env env1) sigma) ms
     ; let f d (ts,ps,t) = displays d [Dl ts ",",Ds " ----> ",Dd t]
     ; morepairs <- hasMonoTypeFun env1 more
     ; rule <- makeRule nm polyt clauses
     ; tree <- case defTree rule of
                 (t:ts) -> return t
                 [] -> failD 0 [Ds ("\nThe type function "++nm++" is not inductively sequential.\n")
                               ,Ds (show dd)]
     ; return ((nm,tree): morepairs)
     }

makeRule s k xs =
  do { let f (lhsexps,lhspats,rhs) =
              do { let (_,vs,_) = varsOfTau (TyFun s k (rhs:lhsexps))
                       new (nm,kind) = newFlexiTyVar kind
                       pick (nm,kind) var = (nm,TcTv var)
                 ; us <- mapM new vs
                 ; let env = (zipWith pick vs us,[],[],[]) -- TODO LEVEL
                 ; newlhs <- mapM (sub env) lhsexps
                 ; newrhs <- sub env rhs
                 ; return (us,newlhs,newrhs)}
     ; zs <- mapM f xs
     ; return(NarR(NTyCon s k,zs)) }

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
           f s = do { m <- newTau (MK (Star (lv 2)))
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
checkPTBndr current (y@(Tstar n),k) =
  do { let err message =
             failD 3 [Ds "\nWhile kind checking a type function.\n"
                     ,Dd y,Ds " :: ",Dd k,Ds " is not well formed for a lhs."
                     ,Ds message]
     ; handleM 3 (unify (Star (LvSucc n)) k) err
     ; return [] }
checkPTBndr current (Tkarr x y,k) =
  do { env1 <- checkPTBndr current (x,k)
     ; env2 <- checkPTBndr current (y,k)
     ; return(env1++env2) }
checkPTBndr current (y,k) =
  failD 1 [Dd y,Ds " :: ",Dd k,Ds " is not well formed for a lhs."]

getInfo y [] s = failD 1 [Ds "While checking the lhs: ",Dd y,Ds " unknown type: ",Dd s]
getInfo y ((x,tau,k):xs) s = if s==x then return (tau,k) else getInfo y xs s


-- ====================================================================
-- We use Lemmas to try and establish narrowing equalities about type-level
-- function that have ambiguous solutions. I.E we are left with
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

applyLemmas [] term = return Nothing
applyLemmas ((lemma,(vs,preds,lhs,rhs)):more) term =
  case match [] [(lhs,term)] of
    Just u1 -> do { let new = subTau u1 rhs
                        preconds = (subPred u1 preds)
                  ; verbose <- getMode "theorem"
                  ; whenM verbose [Ds ("\n*** Trying lemma '"++rname lemma++"' on term:\n   ")
                                  ,Ds "[" ,Dl preconds ",",Ds "] => "
                                  ,Dd term,Ds "  --->  ",Dd new
                                  ]
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


defTreeInfo s =
 do { table <- getTyFuns
    ; let p (nm,tree) = nm==s
    ; return (find p table)
    }

--  normalizes a TyFun term by "match"ing it against all the
-- leaves in the DefTree for that function. "applyTree" is written
-- in continuation passing style (at the computation level)
-- It also applys lemmas if no function definition matches.


normTyFun :: String -> PolyKind -> [Tau] -> TC Tau
normTyFun "(==)" k [x,y] = return(TyFun "(==)" k [x,y])
normTyFun s k ts =
   do {norm_ts <- mapM nf ts
      ; let new = (TyFun s k norm_ts)
            found (nm,tr) = return tr
            notFound = (failM 0 [Ds "2) Unknown type function: ",Ds s])
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
     -- ; warnM [Ds "\nTrying normEqual on ",Dd x ,Ds " == ",Dd y]
     ; let new = (teq x1 y1)
     ; maybeM (applyLemmas rs new)
              (\ (newer,u2) -> return newer)
              (return new)}


applyTree :: (DefTree TcTv Tau) -> Tau -> TC Tau -> TC Tau
applyTree (Leaf pat free lhs rhs) term next =
 do { (lhs2,rhs2) <- freshX (free,lhs,rhs)
    ; case match [] [(lhs2,term)] of
        Just unifier ->
           do { let rewritten = subTau unifier rhs2
              ; verbose <- getMode "narrowing"
              ; whenM verbose [Ds "Norm ",Dd term, Ds " ---> ", Dd rewritten,Ds "\n"]
              ; nf rewritten }
        Nothing -> next }
applyTree (Branchx pattern path trees) term next = first trees term
  where first [] term = next
        first (t:ts) term = applyTree t term (first ts term)

-- ====================================================================
-- Narrowing

solveByNarrowing :: (Int,Int) ->(String,Rho) -> [Pred] -> [(Tau,Tau)] -> TC [(TcTv,Tau)]
solveByNarrowing (nsol,nsteps) context truths [] = return []
solveByNarrowing (nsol,nsteps) context@(s,_) truths xs =
    do { whenM False
              [ Ds ("\n***********************\nIn solve: "++s)
              , Ds "\nEquations = ",Dl xs "; "
              ,Ds "\nTruths = ",Dl truths "; "];
         tests <- zonk xs
       ; let ordered = sortBy lessTau tests
       ; let conj = andP(map EqP ordered)
             hyp = andR(map EqR (foldr pred2Pair [] truths))
             originalVar = mentionsFree tests
       ; conj2 <- nf conj
       ; hyp2 <- nf hyp
       ; reportEnter context conj conj2 truths
       ; (d2,cntxt) <- showThruDisplay [dProb conj2]
       ; (ans2,(_,_,d3,exceed)) <- narr cntxt (nsteps,nsol,d2,False) [(conj2,hyp2,[])] []
       ; let termOf (TermP x,ts,un) = (x,un)
             termOf (EqP(x,y),ts,un) = (teq x y,un)
       ; result <- if exceed
            then do {(solvedByDecProc) <- tryCooper (foldr pred2Pair [] truths) conj
                    ; if solvedByDecProc
                         then return[]
                         else failM 0 [Ds "Solving the equations: ",Dd tests
                                      ,Ds " exceeded narrowing resources."]}
            else case map termOf ans2 of
                  [(xinstan,unifier)] -> mapM checkKind (filter originalVar unifier)
                  [] -> failM 0 [Ds "The equations: ",Dd tests,Ds " have no solution"]
                  others -> moreThanOne context truths originalVar conj others
       ; reportExit result
       ; zonk result}

newToOld ex ans = (if ex then Exceeded else Answers)(map g ans)
  where g (TermP x,ts,un) = (x,un)
        g (EqP(x,y),ts,un) = (teq x y,un)


moreThanOne context truths originalVar x others =
 do { solvedByDecisionProc <- tryCooper (foldr pred2Pair [] truths) x
    ; case (x,solvedByDecisionProc) of
        (_,True) -> return []
        (EqP(x,y),_) ->
            (maybeM (useLemma (Equality x y))
                    (\ u -> exit x (Just u))
                    (exit x Nothing))
        (other,_) -> exit x Nothing}
 where proj (t,u) = filter originalVar u
       short = map proj others
       contextElem (name,Rtau(Star LvZero)) =
           Ds ("While infering the type for: "++name)
       contextElem (name,rho) =
           Dr [Ds ("\nWhile checking: "++name++":: "),Dd rho]
       exit origterm (Just u) = return u
       exit origterm Nothing = failM 2
          [contextElem context
          ,Ds "\nWe had to solve the narrowing problem:\n  "
          ,Dd origterm
          ,Ds "\nUnder the truths\n ",Dl truths "\n "
          ,Ds "\nBut, it has ambiguous solutions:\n  "
          ,Dl short "\n  "]

-----------------------------------------------------------------
-- To solve by narrowing we need some helper functions


lessTau (x,y) (a,b) = compare (count a+count b) (count x+count y)
   where count (TyFun nm k xs) = 0
         count (TyCon _ nm k) = 2
         count (Star n) = 2
         count (TySyn nm n fs vs x) = count x
         count x = 1

reportEnter p conj normf truths =
 do { verbose <- getMode "narrowing"
    ; rs <- getLemmas
    ; whenM verbose
         [Ds "\n####################c"
         ,Ds "\nSolve By Narrowing: ", Dd conj
         ,Ds "\nCollected by type checking in scope case ",Ds (fst p)
         ,Ds "\nNormal form: ",Dd normf
         ,Ds "\nAssumptions: ",Dd truths
         ,Ds "\n   Theorems: ",Dl rs "\n             "]}

reportExit ans =
 do { truths <- getAssume
    ; verbose <- getMode "narrowing"
    ; whenM verbose [Ds "\nAnswers = ", Dd ans,Ds "\nTruths = ",Dd truths]
    }

mentionsFree termL = ok
  where free = foldr union [] (map tvsTau (map (uncurry TyApp) termL))
        ok (v,term) = elem v free



checkKind (v@(Tv n f (MK k)), term) =
  do { term' <- check term k; return(v,term') }


-- ====================================================================
-- Coopers Algorithm for solving Pressburger Arithmetic

tryCooper :: [(Tau,Tau)] -> Prob Tau -> TC Bool
tryCooper truths x =
  do { let xnorm = prob2Tau x
     ; truthsnorm <- nf truths
     ; xZonk <- zonk xnorm
     ; truthsZonk <- zonk truthsnorm
     ; (d3,_) <- showThruDisplay [Dd truthsZonk,Dd xZonk]
     ; case (toFormula (mapfromDI d3) truthsZonk xZonk) of
         Just (allform, form) ->
           do { warnM [Ds "\nUsing the decision procedure to check:\n"
                      ,Ds (show allform)]
              ; ans <-  handleM 3 (integer_qelim allform)
                         (\ mess -> warnM [Ds ("The decision procedure failed with the message: "++mess)]
                          >> return FalseF)

              ; case ans of
                  TrueF -> do { warnM [Ds "\nGOOD ans = ",Ds (show ans)]; return(True)}
                  _ -> do { warnM [Ds "\nBAD ans = ",Ds (show ans)]
                          ; ans2 <- integer_qelim form
                          ; warnM [Ds "Non quantified =\n",Ds (show ans2)]
                          ; return (False) }
              }
         Nothing -> return (False)}

prob2Tau :: Prob Tau -> Tau
prob2Tau (TermP x) = x
prob2Tau (EqP(x,y)) = teq x y
prob2Tau (AndP ps) = foldr1 andf (map prob2Tau ps)

-- =====================================================================
-- Tpat are used for matching against Rules, which are used to Solve
-- backchaining predicates.

data Tpat
  = Tvar String Name
  | Tcon String [ Tpat ]
  | Tstar Level
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
pTtoTpat (Star' n) e1 = return(e1,Tstar (lv n))
pTtoTpat (TyFun' (TyVar' s : xs)) e1 =
  do { (e2,ys) <- thrd e1 pTtoTpat xs
     ; return(e2,Tfun s ys) }
pTtoTpat x e1 = fail ("The type: "++show x++" is not appropriate for the LHS of a type fun.")

thrd e1 f [] = return(e1,[])
thrd e1 f (x:xs) = do { (e2,y) <- f x e1; (e3,ys) <- thrd e2 f xs; return(e3,y:ys)}

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

data RuleClass = Axiom | BackChain | Rewrite deriving Show


--               name   key    class     Vars                Precond Lhs  Rhs
data RWrule = RW String String RuleClass [(Name,Kind,Quant)] [Pred]  Pred [Pred]
--                                       Quant=Ex if Name not in LHS

axiom (RW nm key Axiom args precond lhs rhs) = True
axiom _ = False

rname (RW nm key rclass args precond lhs rhs) = nm
rkey  (RW nm key rclass args precond lhs rhs) = key
isLemma (RW nm key Rewrite vs pre lhs rhs) = True
isLemma (RW nm key _ vs pre lhs rhs) = False
zonkRW (RW nm key cl vs pre lhs rhs) =
  do { a <- zonk pre; b <- zonk lhs; c <- zonk rhs; return(RW nm key cl vs a b c)}

instance TypeLike (Mtc TcEnv Pred) RWrule where
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



-- ======================================================================
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
-- The second two are irrelevant since they are subsumed by the first two.

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
ruleStep (truths,[],open,u0) = return (Nothing)
ruleStep (truths,q:questions,open,u0) =
   do { s <- predNameFromTau q q
      ; rules <- getMatchingRules s
      ; verbose <- getMode "solving"
      ; when verbose
          (do { warnM [Ds "\nTrying to find evidence for the predicate:\n   ",Dd q
                      ,Ds "\nUnder assumptions:\n   [",Dl truths ", ",Ds "]"
                      ,Ds "\nCurrently solving subproblems from the rules: ",Dl open ","
                      ,Ds "\nPossibly matching rules are\n  ", Dl rules ",\n  ", Ds "\n"]
              ; waitN "solving"
              ; return ()})
      ; infoList <- matchR truths open rules q
      ; whenM verbose
           [Ds "\nExactly ",Dd (length infoList)
           ,Ds " rules match:\n  ",Ds "\n"]
      ; case infoList of
         [] -> do { zs <- ruleStep (truths,questions,open,u0)
                  ; let f13 q (ts,qs,nms,u) = (ts,(subTau u q):qs,nms,u)
                  ; return(fmap (map (f13 q)) zs)}
         ws -> do { good <- foldM goodMatch [] ws
                  ; let fixform (newtruths,rhs,nms,u) =
                          (newtruths,rhs ++ fix questions,nms,composeU u u0)
                           where fix x = map (subTau u) x
                  ; return(Just(map fixform good))}}



goodMatch good (truths,precond,result,open,unifier) =
  do { ans <- solv 4 [(truths,map (unRel 5) precond,open,unifier)]
     ; case ans of
         [(truths2,[],nms,u)] -> return((truths2,map (subTau u) (map (unRel 6) result),open,u):good)
         _ -> return good}

unRel n (Rel x) = x
unRel n x = error ("\nunRel applied to non Rel: "++show x++" "++show n)

exploreD n = length n > 3

matchR ::[Tau] -> [String] -> [RWrule] -> Tau -> TC[([Tau],[Pred],[Pred],[String],Unifier)]
matchR truths openRules [] term = return []
matchR truths open ((r@(RW nm key BackChain _ _ _ _)):rs) term
  | elem nm open = matchR truths open rs term
matchR truths open ((r@(RW nm key _ _ _ _ _)):rs) term
  | exploreD (filter (nm==) open) = matchR truths open rs term
matchR truths open ((r@(RW nm key cl _ _ _ _)):rs) term =
  do { (vars,precond,Rel lhs,rhs) <- freshRule newflexi r
     ; ys <- matchR truths open rs term
     ; case mostGenUnify [(lhs,term)] of
        Just sub -> do { let pre2 = subPred sub precond
                             rhs2 = subPred sub rhs
                       ; verbose <- getMode "solving"
                       ; whenM verbose
                           [Ds "\nMatched term: ",Dd term
                           ,Ds "\n Rewrites to: ",Dd rhs2
                           ,Ds "\n Under subst: ",Dd sub
                           ,Ds "\nPrerequisite: ",Dd pre2]
                       ; return((map (subTau sub) truths,pre2,rhs2,nm:open,sub):ys) }
        Nothing -> return ys
     }

----------------------------------------------------------------------------
-- Solving a list of predicates returns a second list of, hopefully,
-- simpler predicates. If the returned list is empty, then the input
-- is solved.

solveConstraints (context,rho) truths [] = return []
solveConstraints (context,rho) truths cs =
  do { let (ps,eqs,un0) = split3 cs
     -- ; warnM [Ds ("\nSolving constraints in context "++context)
     --       ,Ds "\nTruths = ",Dl truths ","
     --       ,Ds "\ncontraints = ",Dl cs ","]
     ; (ps2,eqs2) <- sub ([],un0,[],[]) (ps,eqs) -- TODO LEVEL
     ; steps <- getBound "narrow" 25
     ; un1 <- solveByNarrowing (3,steps) ("1. "++context,rho) truths eqs2
     ; un2 <- mutVarSolve un1
     ; ps3 <- sub ([],un2,[],[]) ps2 -- TODO LEVEL
     ; truths2 <- expandTruths truths
     --; warnM [Ds "Just before solvP, truths = ",Dl truths ","
     --       ,Ds "; and need = ",Dl ps3 ","]
     ; (ps4,un3) <- (solvP truths2 ps3)
     ; mutVarSolve un3
     ; zonk ps4
     }

solv :: Int -> [([Tau],[Tau],[String],Unifier)] -> TC ([([Tau],[Tau],[String],Unifier)])
solv n [] = return ([])
solv 0 xs = warnM [Ds "\nThe 'backchain' bounds have been exceeded."] >> return ([])
solv n ((ts,[],nms,u):xs) =
  do { (ys) <- solv (n-1) xs
     ; return ((ts,[],nms,u):ys) }
solv n ((x@(ts,qs,nms,u)):xs) =
  case truthStep x of
   [] -> do { m <- ruleStep x
            ; case m of
                Nothing -> do { (ys) <- solv (n-1) xs; return(x:ys)}
                Just ws ->  solv n (xs++ws) }
   zs -> do { whenM False [Ds "Truth Steps\n  ",Dlf f15 zs "\n  "]
            ; solv n (zs++xs)}

f15 d (ts,qs,_,u) = displays d [Ds "[",Dl ts ",",Ds "] => [",Dl qs ",",Ds"]", Ds " where ",Dd u]




solvP :: [Tau] -> [Tau] -> TC([Pred],Unifier)
solvP truths questions =
  do { steps <- getBound "backchain" 4
     ; (ans) <- solv steps [(truths,questions,[],[])]
     ; case ans of
         [] -> failD 3 [Ds "No solution to [",Dl truths ", "
                       ,Ds "] => [", Dl questions ",",Ds "]"]
         [(ts,qs,nms,u)] -> return(map Rel qs,u)
         ((x@(ts,qs,nms,u)):xs) ->
           let aMostGeneral (ts,qs,nms,u) = null u
               axiom [] = False
               axiom (c:cs) = isUpper c
               axiomOnlySolution (ts,qs,nms,u) = all axiom nms
           in case find aMostGeneral (x:xs) of
                Just (ts,qs,nms,u) -> return(map Rel qs,u)
                Nothing -> case filter axiomOnlySolution (x:xs) of  -- Look for a Unique one
                             [(ts,qs,nms,u)] -> return(map Rel qs,u)
                             other -> failM 2 [Ds "Ambiguous solutions to: [",
                                              Dl truths ",",Ds "] => [",Dl questions ",",Ds "]\n   ",
                                              Dlf g45 (x:xs) "\n   "]
     }

g45 d (ts,ps,nms,u) = displays d [Ds "questions [",Dl ps ",",Ds "] unifier ",Dd u,Ds " rules used ",Dl nms ","]


expandTruths truths =
  do { let (ps,eqs,un0) = split3 truths
     ; whenM (not (null eqs)) [Ds "Non null Narrowing questions in expandTruths:\n  ",Dl eqs ","]
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
checkTau ((r@(RW nm key Rewrite _ _ _ _)):rs) truth = checkTau rs truth
checkTau ((r@(RW nm key BackChain _ _ _ _)):rs) truth = checkTau rs truth
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



-- =================================================================
-- effect free unifiers and their operations

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

     ; whenM True [Ds ("\nmguM "++s),Ds "\n preds = ",Dd preds
            ,Ds "\nother = ", Dl other ", "
            ,Ds "\nhard = ",Dl hard ", "
            ,Ds "\neasy = ",Dl easy ", "
            ,Ds "\n unifier1 = ",Dd unifier1]

     ; maybe <- unifierFromEasyTruths other easy
     ; (ps2,unifier2) <- case maybe of
                          Nothing -> failK "mguErr" 2 [Ds "Contradiction"]
                          Just(hard,u) -> return(hard,u)
     ; let u3 = composeMGU unifier2 unifier1
           eqs = map (\ (Equality x y) -> (x,y)) (subPred u3 hard)
     -- ; warnM [Ds "\nMGUM unifier2 = ",Dd unifier2,Ds " eqs = ", Dd eqs]
     ; truths <- getTruths
     ; steps <- getBound "narrow" 25
     ; u4 <- solveByNarrowing (3,steps) ("4."++s,r) truths eqs
     ; let u5 = composeMGU u4 u3
     -- Failure of MutVarSolve means some kind of inconsistency
     -- Occurs check  when we have  (a = {plus a Z}) for example
     ; u6 <- mutVarSolve u5
     ; ps3<- zonk ps2
     ; ps4 <- sub ([],u6,[],[]) ps3 -- TODO LEVEL
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
  do { d0 <- readRef dispRef
     ; let (d1,cntxt) = displays d0 [dProb (EqP(x,y))]
     ; writeRef dispRef d1
     ; (sols,(_,_,d2,exceeded)) <- narr cntxt (10,2,d1,False) [(EqP(x,y),andR[],[])] []
     ; warnM [Ds "\nexit from narr in unifierFromEasyTruths"]
     ; case (exceeded,sols) of
         (False,[]) -> return Nothing -- A contradiction !
         (False,[(term,truths,u1)]) ->  -- Where hoping if exceeded is True!!
              do { ps2 <- sub ([],u1,[],[]) ps
                 ; hard2 <- sub ([],u1,[],[]) hard
                 ; maybeM (unifierFromEasyTruths hard2 ps2)
                          (\ (hard3,u2) -> return(Just (hard3,composeMGU u2 u1)))
                          (return Nothing)} -- propogate contradictions
         (True,[(term,truths,u1)]) ->
              do { warnM [Ds "\nWe ran out of narrowing resources solving:\n"
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


-- =====================================================
-- Display, Exhibit, and Show of datatypes in Infer2
-- To Display a name, prints it in a more concise manner by
-- maintaining a list of concise names for each Var encountered.

instance NameStore d => Exhibit d [(Var,(Sigma,CodeLevel,Exp))] where
  exhibit xs [] = (xs,"")
  exhibit xs ys = exhibitL exhibit xs ys "\n   "

instance NameStore d => Exhibit d (Var,(Sigma,CodeLevel,Exp)) where
  exhibit xs (v,(s,l,e)) = (zs,show v++": "++ans)
   where (zs,ans) = exhibit xs s

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

instance Exhibit (DispInfo Z) [String] where
  exhibit d1 s = (d1,plist "[" s "," "]")

instance Exhibit (DispInfo Z) Lit where
  exhibit d1 c = (d1,show c)
instance Exhibit (DispInfo Z) Exp where
  exhibit d1 c = (d1,show c)

instance Exhibit (DispInfo Z) (Exp,Expected Rho) where
  exhibit d1 (e,Check x) = displays d1 [Dd e, Ds ":: (Check ",Dd x,Ds ")"]
  exhibit d1 (e,Infer ref) = displays d1 [Dd e, Ds ":: Infer"]

instance Exhibit (DispInfo Z) (Exp,Tau) where
  exhibit d1 (e,x) = displays d1 [Dd e, Ds ":: ",Dd x]

instance Exhibit (DispInfo Z) Constr where
  exhibit d (Constr _ targs c doms Nothing) =
    displays d [Ds "exists ",Dlf hf targs ",",Ds " . ",Ds (show c++" ")
               ,Dl doms ", "]
  exhibit d (Constr _ targs c doms (Just ps)) =
    displays d [Ds "exists ",Dlf hf targs ",",Ds " . ",Ds (show c++" ")
               ,Dl doms ", ",Ds " where ",Dl ps ", "]

hf d (Global s,pt) = displays d [Ds ("("++show s++","), Dd pt, Ds ")"]

instance Exhibit (DispInfo Z) RWrule where
  exhibit d (RW nm key Rewrite vars pre lhs [rhs]) =
    displays d [Ds "Rewrite ",Ds (nm++": ")
               ,Ds "[", Dl pre ", ", Ds "] => "
               ,Dd lhs,Ds " --> ",Dd rhs]
  exhibit d (RW nm key rclass vars pre lhs rhs) =
    displays d [Ds (show rclass++" "++nm++": ")
               ,Dlg f "(exists " (foldr exf [] vars) "," ") "
               ,Ds "[", Dl pre ", ", Ds "] => ",Dd lhs,Ds " --> [",Dl rhs ", ",Ds "]"
              ]
   where f d (nm,k) = useStoreName nm k id d
         exf (nm,k,Ex) xs = (nm,k):xs
         exf (_,_,All) xs = xs

instance Exhibit (DispInfo Z) Mod where
  exhibit d Wob = (d,"Wobbly")
  exhibit d Rig = (d,"Rigid")

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


-- =====================================================
-- Initializing the type environment
--------------------------------------------------------

trans0 s = (readName "In trans0: ") typeConstrEnv0 s

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
 "data Bool:: *0 where\n"++
 "  True:: Bool\n"++
 "  False:: Bool\n"++
 "data Maybe:: *0 ~> *0 where\n"++
 "  Just :: a -> Maybe a\n"++
 "  Nothing :: Maybe a\n"++
 "data Prop :: *1 where\n"++
 "  Success :: Prop\n"++
 "and:: Prop ~> Prop ~> Prop\n"++
 "{and Success x } = x\n"++
 "data Nat :: *1 where\n"++
 "  Z :: Nat\n"++
 "  S :: Nat ~> Nat\n"++
 "prop Nat' :: Nat ~> *0 where\n"++
 "  Z:: Nat' Z\n"++
 "  S:: forall (a:: Nat) . Nat' a -> Nat' (S a)\n"++
 --"data Equal a b = Eq where a=b\n"++
 "data Equal :: forall (a:: *1) . a ~> a ~> *0 where\n"++
 "  Eq:: forall (b:: *1) (x:: b) . Equal x x\n"++
 "data EqTag :: Tag ~> Tag ~> *0 where\n"++
 "  EqTag:: EqTag x x\n"++
 "data HasType :: *1 where\n"++
 "  Has :: Tag ~> *0 ~> HasType\n"++
 "data Row :: *1 ~> *1 where\n"++
 "  RCons :: x ~> (Row x) ~> Row x\n"++
 "  RNil :: Row x\n"++
 "data Monad :: (*0 ~> *0) ~> *0 where\n"++
 "  Monad :: forall (m:: *0 ~> *0) .\n"++
 "                  ((forall a . a -> m a)) ->\n"++
 "                  ((forall a b . (m a) -> (a -> m b) -> m b)) ->\n"++
 "                  ((forall a . String -> m a)) ->\n"++
 "                  Monad m\n"


-- Parse the predefined data decls
-- then do a topological sort.
preDefDec = dss
  where (Right(Program ds,_)) = parse2 program predefined
        (dss,pairs) = topSortR freeOfDec ds

-- Go through each binding group in the topological sort
-- and transform the environment

decMany :: [[Dec]] -> TcEnv -> FIO TcEnv
decMany [] env = return env
decMany (ds:dss) env =
  do { (env2,_,_) <- checkDecs env ds
     ; rt_env <- elaborate None ds (runtime_env env2)  -- evaluate the list
     ; let env3 = (env2 { runtime_env = rt_env })
     ; decMany dss env3}

look2 :: IO[()]
look2 = showAllVals 1000 tcEnv0

-- ===========================================================================
-- The interactive type checking loop
-- Loop until "f" says quit (continue == True), catch all errors
-- but continue looping after reporting them

interactiveLoop :: (env -> TC Bool) -> env -> TC ()
interactiveLoop f env = handleM 3
  (do { (continue) <-  (f env)
      ; if continue then interactiveLoop f env else return ()
      }) (\ s -> do {outputString s; interactiveLoop f env})

-- use the ReadLine library to enable line editing
-- pass a prompt and a tab expansion function

lineEditReadln :: String -> (String -> [String]) -> FIO String
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

updateDisp :: TC ()
updateDisp = do { x@(DI (bs,bad,names)) <- readRef dispRef
                ; new <- reset bs
                ; writeRef dispRef (DI(new,bad,names))}
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


waitN mode =
  do { line <- getS "press return to step, 'c' to continue:\n" (\ _ -> [])
     ; case line of
         "c" -> setMode mode False >> return ()
         _ -> return ()}


checkReadEvalPrint :: (Expected Rho,TcEnv) -> TC Bool
checkReadEvalPrint (hint,env) =
  do { let tabExpandFun = completionEntry env
     ; input <- getS "check> " tabExpandFun
     ; z <- parseString pCommand input
     ; case z of
        Left s -> do {putS s; return (True) }
        Right(x,rest) ->
         case x of
          (ColonCom "set" s) -> fio2Mtc(setCommand s True (True))
          (ColonCom "q" _) -> return (False)
          (ColonCom "rules" s) ->
             do { let rs = getRules s env
                ; warnM [Ds "rules\n",Dl rs "\n  "]
                ; return(True)
                }
          (ColonCom "e" _) ->
             do { truths <- zonk (assumptions env)
                ; warnM [Ds "truths: ",Dd truths,Ds ("\n  "++shtt truths)]
                ; return (True) }
          (ColonCom "h" _) ->
             do { warnM [Ds "Hint = ",Dd hint]
                ; return(True)
                }
          (ColonCom "k" x) ->
             do { (k,t,tree) <- getkind x env
                ; putS (x++" :: "++(pprint k)++"\n" ++ pprint t ++ "\n"++tree)
                ; return (True) }
          (ColonCom "t" x) ->
             case getVar (Global x) env of
                Just(sigma,mod,lev,exp) ->
                   do { s1 <- zonk sigma
                      ; updateDisp
                      ; warnM [Ds (x ++ " :: "),Dd s1]
                      ; return (True)}
                Nothing -> do { putS ("Unknown name: "++x); return (True)}
          (ColonCom "o" e) ->
             do { exp <- getExp e
                ; (t,exp2) <- inferExp exp
                ; t1 <- zonk t
                ; updateDisp
                ; warnM [Ds (show exp ++ " :: "),Dd t1]
                ; return (True)
                }
          (ColonCom "try" e) ->
             do {  exp <- getExp e
                ; (_,oblig) <- collectPred (tc exp hint)
                ; obs <- zonk oblig
                ; updateDisp
                ; warnM [Ds(show exp ++ " :: "),Dd hint]
                ; whenM (not (null oblig)) [Ds "Only when we can solve\n   ",Dd obs]
                ; return (True)
                }
          (ExecCom exp) ->
             do { ((t,e2),oblig) <- collectPred (inferExp exp)
                ; t2 <- zonk t
                ; obs <- zonk oblig
                ; updateDisp
                ; warnM [Ds(show exp ++ " :: "),Dd t2]
                ; whenM (not (null oblig)) [Ds "Only when we can solve\n   ",Dd obs]
                ; return (True)
                }
          other -> putS "unknown command" >> return (True)
     }

checkLoop :: Expected Rho -> TcEnv -> TC ()
checkLoop typ env = interactiveLoop checkReadEvalPrint (typ,env)

-- ==================================================================
-- The Circuit extension

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

--------------------------------------------------------------
-- Translating Circuit expressions
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

okCircuitDec (Val loc (Pvar s) (Normal e) []) = Nothing
okCircuitDec d = Just d

allOk ds = f maybes
  where maybes = map okCircuitDec ds
        f [] = return ()
        f (Nothing : xs) = f xs
        f (Just d: xs) = fail ("Illegal binding in circuit:\n  "++show d)

hasMonoType (var,(Forall (Nil ([],Rtau t)),mod,_,_)) = return (var,t)
hasMonoType (var,x) = fail (show var++" does not have a monomorphic type")

transForm (v,TyApp (TyCon l "Exp" k) t) = return ("Exp1",v,toRep t)
transForm (v,TyApp (TyApp (TyApp (TyCon l "Exp" k) c) row) t) = return ("Exp3",v,toRep t)
transForm (v,TyApp (TyCon l "Sig" k) t) = return ("Sig1",v,toRep t)
transForm (v,z) = fail (show v++"::"++show z++" is not a circuit type")

allSameForm x [] = return []
allSameForm x ((y,v,t):xs) | x==y = do {ys <- allSameForm x xs; return((v,t):ys)}
allSameForm x ((y,v,t):xs) = failD 1 [Ds "The declaration for ",Dd v,Ds " doesn't match the other declarations"]

collect2 [] [] = return (0::Int,[])
collect2 ((nm1@(Global name),typ):xs) ((nm2,exp):ys) | nm1==nm2 =
  do { (n,zs) <- collect2 xs ys
     ; return (n+1,(n,name,typ,exp):zs) }
collect2 _ _ = fail "Names don't correspond with declarations in circuit"

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

gensym s = do { n' <- fresh
              ; return(Pvar(Alpha s n'),Var(Alpha s n'))}

toRep (TyCon l "Bit" k) = Var (Global "Bit")
toRep (TyCon l "Int" k) = Var (Global "Int")
toRep (TyCon l "Z" k) = Var (Global "Z")
toRep (TyApp (TyCon l "S" k) x) = App (Var (Global "S")) (toRep x)
toRep (TyApp (TyApp (TyCon l "(,)" k) x) y) =
  (App (App (Var (Global "Prod")) (toRep x)) (toRep y))
toRep (TyApp (TyApp (TyCon l "Vec" k) x) y) =
  (App (App (Var (Global "Vec")) (toRep x)) (toRep y))


-- Each type of circuit will need a different kind of substitution applied
-- to each RHS and the (In TERM), Given "f" we can construct such a substitution

circuitSub :: (Int -> String -> Exp -> Exp) -> (Int,String,Exp,Exp) -> (Var,Exp)
circuitSub f (n,label,typ,body) = (Global label,f n label typ)

-- Then the substitution can be applied with this function

subNew subst (n,label,typ,exp) =
     do { exp1 <- subExp subst exp; return(n,label,typ,exp1) }

stringLit s = listExp (map (Lit . Char) s)
labelLit s = Lit(Tag s)

appE [x] = x
appE (x:y:xs) = appE ((App x y):xs)

-- Make a substitution for (Exp t) forms
subExp1 xs = map (circuitSub f) xs
  where f n nm typ = appE [Var (Global "Var"),stringLit nm,typ]

-- Make a substitution for (Exp c env t) forms
subExp3 total xs = map (circuitSub shiftf) xs

shiftf n nm typ =
   shift n (appE [Var (Global "Var"),labelLit nm])

shift 0 e = e
shift n e = App (var "Sh") (shift (n-1) e)

-- ============================================================================
-- Theorems are added by the "theorem" decl
-- There are two uses for theorems
-- 1) As left to right rewrite rules. The type has the form (Equal lhs rhs)
--    the lhs must be a Type constructor call, or a type function call
-- 2) Backchaining rule: P x -> Q y -> S x y   where P,Q, and S are propositions
--    Replace (S x y) with the set {P x, Q y}

-- Look at the structure of a type and determine what kind of theorem it could be.

data TheoremSplit
  = Chain (String,[Pred],Tau)
  | LeftToRight (String,[Pred],Tau,Tau)
  | NotATheorem

whatKind :: Maybe RuleClass -> Rho -> TC TheoremSplit
whatKind thclass rho =
  do { (doms,rng) <- rhoArrowParts rho
     ; case equalPartsM rng of
         Just(x,y) ->
            case (x,rootT x []) of
             (TyFun f _ _, any) -> return(LeftToRight(f,map Rel doms,x,y))
             (any,Just(f,k,zs)) -> return(LeftToRight(f,map Rel doms,x,y))
             _ -> failD 2 [Ds message4,Dd rng]
         Nothing -> let tname = root thclass rng
                    in ifM (allM (isProp tname) (rng:doms))
                           (return (Chain(tname,map Rel doms,rng)))
                           (return NotATheorem)
     }

-- When adding axioms, we need to assume the type being defined
-- is a proposition, since it hasn't been added to the list of
-- propositions yet, so we must tell isProp this. let the theorem
-- be a type like: dom1 -> dom2 -> rng,   where rng = (T x y z)

root (Just Axiom) rng =
   case rootT rng [] of
     Just(tname,kind,args) -> tname
     Nothing -> ""
root _ rng = ""

message4 =
 "\nIn a rewrite rule, the lhs must be a type-function call (like {plus x y}) or\n" ++
 "a type-constructor application (like (Even x)), otherwise it can't be\n" ++
 "used as a rewrite rule. This is not the case for:\n  "

sigmaToRule rclass (name,sigma) =
 do { x <- instanTy sigma           -- The instanTy, generalize sequence
    ; (Forall xs) <- generalize x   -- removes Equality predicates
    ; (args,(conds,rho)) <- unwind xs
    ; let thclass = case rclass of
                      Nothing -> BackChain
                      (Just c) -> c
    ; info <- whatKind rclass rho
    ; case info of
        LeftToRight(key,precond,lhs,rhs) ->
          return[(key,RW name key Rewrite args (precond++conds) (Rel lhs) [(Rel rhs)])]
        Chain(key,doms,rng) ->
          let (_,bound,_) = varsOfTau rng
              (_,fr,_) = varsOfPred (doms ++ conds)
              eq (nm1,k1) (nm2,k2) = nm1==nm2
              free = deleteFirstsBy eq fr bound
              g (nm,k,q) = if any (eq (nm,k)) free then (nm,k,Ex) else (nm,k,All)
              args2 = map g args
              lhs = Rel rng
              rhs = if (null free) then doms else []
              preCond = conds ++ (if (null free) then [] else doms)
              ans = [(key,RW name key thclass args2 preCond lhs rhs)]
          in return ans
        NotATheorem -> (warnM [Ds "\nIn the theorem '",Ds name, Ds "' the type: ",Dd rho
                              ,Ds "\nis neither a back-chaining or a left-to-right rewrite rule."
                              ,Ds "\nThus, no rule is added.\n"])
                        >> (return[])

    }

rhoArrowParts (Rtau z) = return(down [] z)
  where down xs (TyApp (TyApp (TyCon _ "(->)" _) x) y) = down (x:xs) y
        down xs z = (reverse xs,z)
rhoArrowParts r =
   failM 3 [Ds "\nThe type for a theorem cannot be a rankN type yet:\n", Dd r]

isProp:: String -> Tau -> TC Bool
isProp new t =
  case rootT t [] of
   Just(s,k,xs) | s==new -> return True
   Just(s,k,xs) -> do { env <- tcEnv;
                      ; return(Map.member s (rules env)) }
   Nothing -> return False

computeTheorems :: [(Var,Maybe Exp)] -> TC [(String,RWrule)]
computeTheorems names =
    do { rss <- mapM f names
       ; let rs = concat rss
       ; verbose <- getMode "theorem"
       ; whenM verbose [Ds "\nAdding theorem\n  ",Dl (map snd rs) "\n  "]
       ; mapM znk rs }
  where f (v@(Global nm),Nothing) =
          do { (sigma,mod,n,exp) <- lookupVar v
             ; sigmaToRule Nothing (nm,sigma) }
        f (Global nm,Just term) =
          do { (sigma,_) <- infer term
             ; sigmaToRule Nothing (nm,sigma) }
        znk (name,rule) = do { r2 <- zonkRW rule; return(name,r2)}

-- ==================================================================
-- This is the stuff that is exported for other modules to use.
-- Some of it must run in FIO rather than MTC
-- A version in the FIO monad that returns unresolved NEED as well
-- as the final TcEnv and the transformed Decs, This is the function Exported

checkDecs :: TcEnv -> [Dec] -> FIO (TcEnv,[Dec],[Pred])
checkDecs env ds =
   do { writeRef dispRef disp0 -- Reset Display for each new toplevel Binding group
      ; ((a,b),c) <- unTc (checkAndCatchGroundPred ds) env
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
     ; injectA " checkAndCatch " unsolved
     ; return(ds,env)
     }

checkBndGroup :: [Dec] -> TC([Dec],TcEnv)
checkBndGroup [d@(AddTheorem loc xs)] =
  do { env <- tcEnv
     ; theorems <- newLoc loc (computeTheorems xs)
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
     ; pairs <- hasMonoTypeFun env2 ds2
     ; let env4 = env2{tyfuns = pairs ++ tyfuns env2}
     ; return(ds2,env4)}
checkBndGroup ds | all isData ds =
  do { (sigma,frag,ds2) <- checkDataDecs (useTypeSig ds)
     ; env <- (letExtend frag tcEnv)
     ; return(ds2,env)
     }
checkBndGroup ds =
  do { (frag,ds2) <- inferBndrForDecs False ds
     ; env <- letExtend frag tcEnv
     ; return(ds2,env)
     }


----------------------------------------------------------
-- used for the   x <- iocomputation   command

ioTyped :: TcEnv -> Pat -> Exp -> FIO (Exp,Pat,TcEnv,Tau)
ioTyped env p e =
  tcInFIO env
    (do { a <- newTau star
        ; e' <- check e (Rtau (TyApp ioT a))
        ; (frag,p') <- checkBndr False Wob nullFrag (simpleSigma a) p
        ; a' <- zonk a
        ; return (e',p',addFrag frag env,a')
        })

---------------------------------------------------------
-- Used for the evaluating command

wellTyped :: TcEnv -> Exp -> FIO (Sigma,Exp)
wellTyped env e = tcInFIO env
  (do { ((t::Rho,term),oblig) <- collectPred(inferExp e)
      ; truths <- getAssume
      -- ; warnM [Ds "Obligations at top level are: ",Dd oblig]
      ; oblig2 <- solveConstraints (show e,t) truths oblig
      ; typ <- nfRho t
      ; when (not(null oblig2) && not(arrowP typ))
             (failD 0 [Ds "Unresolved obligations: ",Dl oblig2 ", "
                      , Ds " => ", Dd typ])
      -- ; warnM [Ds "\nt = ",Dd t2, Ds "\ntyp = ",Dd typ]
      ; sigma <- generalize(oblig2,typ)
      ; s2 <- return sigma -- nf sigma
      ; return(s2,term)})

arrowP (Rarrow _ _) = True
arrowP (Rtau (TyApp (TyApp (TyCon l "(->)" k) x) y)) = True
arrowP _ = False


tcInFIO :: TcEnv -> TC x -> FIO x
tcInFIO env e =
  do { (x,ns::[Pred]) <- unTc e env
     ; if null ns
          then return x
          else fail ("\nUnresolved NEED: "++show ns)}

-------------------------------------------------------------------
-- Used for the :narrow command
narrowString env count s =
  do { map1 <- getTypeEnv
     ; (n,parseT) <- (parseIntThenType count s)
     ; let free = getFree [] parseT
     ; outputString (show free)
     ; (map2,vs,us) <- genericEnv free
     ; ty <- toTau (map1++map2) parseT
     ; (k::Tau,newTau) <- infer ty
     ; d0 <- readRef dispRef
     ; let (d1,cntxt) = displays d0 [Dd newTau]
     ; writeRef dispRef d1
     ; (sols,(_,_,d1,ex)) <- narr cntxt (20,n,d1,False) [(TermP newTau,andR[],[])] []
     ; showSols us (newToOld ex sols)
     ; return env
     }

genericEnv free = foldrM acc ([],[],[]) free
  where acc s (ts,vs,us) =
          do { k <- newTau star1
             ; tau@(TcTv u) <- newTau (MK k)
             ; return((s,tau,poly (MK k)):ts,(ZTv u,s):vs,u:us)}

showSols free (Answers []) = return ()
showSols free (Exceeded []) = warnM [Ds "\n*** Narrowing resources exceeded. ***\n"] >> return()
showSols free (Answers ((x,u):zs)) =
  do { warnM [Dd x,Ds "\n  ",Dl (trim free u) "\n  ",Ds "\n"]
     ; showSols free (Answers zs) }
showSols free (Exceeded ((x,u):zs)) =
  do { warnM [Dd x,Ds "\n  ",Dl (trim free u) "\n  ",Ds "\n"]
     ; showSols free (Exceeded zs) }


trim free xs = filter p xs
  where p (nm,ty) = elem nm free

-------------------------------------------------------------
-- used for the   :t type-exp     command

parseAndKind :: TcEnv -> [Char] -> FIO (Kind,Tau)
parseAndKind env s = tcInFIO env
    (
    do { map1 <- getTypeEnv
       ; s <- toTau map1 (parsePT s)
       ; (tau::Tau,s2) <- infer s
       ; return(MK tau,s2)
       -- ; return(MK (kindOf s2),s2)
       })

