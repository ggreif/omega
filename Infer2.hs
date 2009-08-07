module Infer2 where

import PureReadline
import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import System.IO.Unsafe(unsafePerformIO)

import Monad(when,foldM,liftM,filterM)
import Monads(Mtc(..),runTC,testTC,unTc,handleTC,TracksLoc(..)
             ,Exception(..), fixMtc
             ,FIO(..),fio,failP,fio2Mtc,runFIO,io2Mtc
             ,HasNext(..),outputString
             ,extractAccum,injectAccum
             ,readRef,newRef,writeRef,HasIORef()
             ,writeln,readln
             )
import qualified Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.HughesPJ(Doc,text,int,(<>),(<+>),($$),($+$),render)
import Bind
import Syntax
import RankN(Sht(..),sht,univLevelFromPTkind,pp
            ,Quant(..),TcTv(..),Tau(..),Rho(..),Sigma(..),Kind(..),PolyKind(..)
            ,ForAllArgs,ToEnv,PPred,PT(..),MGU,Unifier,Unifier2,Z(..),Expected(..),L(..)
            ,Pred(..),PPred(..),Flavor(..),Level(..),TcLv(..)
            ,newLevel,unifyLevel,pruneLv,freshLevels,incLev,zonkLv,unifyLev,substLevel,instanLevel
            ,TyCh(..),TypeLike(..),Typable(..),Exhibit(..),Subsumption(..),Zonk(..)
            , zonkRho, zonkSigma, zonkTau
            ,NameStore(..),useStoreName, showMdisp
            , makeRel , equalPartsM
            ,failD,failK,failM,warnM,handleM,whenM
            ,dispRef,subTau,subRho,subSigma,sub2Tau,sub2Rho,sub2Sigma,sub2Pred,subTcTv
            ,extendref, failIfInConsistent
            ,mguStar,star1,star,star_star,starR,shtt,shtP  -- splitU,split3,
            ,newKind,newSigma,newFlexiTyVar,newRigidTyVar,newTau,newRigid,newRho,newflexi,newStar
            ,existsInstance,rigidInstance,rigidInstanceL,generalize,instanL,newSkolem
            ,instanTy,instanPatConstr,checkArgs,nameOf
            ,mguB,mostGenUnify,unify,morepolySS,morepolyRR,match2,alpha,morepolySigmaRho
            ,sigmaPair,sigmaSum,unifyCode,unifyFun
            ,poly,simpleSigma,toSigma,toTau,toEqs,toRho,toPT,rho2PT,toL
            ,windup,unsafeUnwind,unBindWith,unwind
            ,varsOfTau,varsOfRho,varsOfSigma,varsOfPred,varsOfPair,varsOfPoly,varsOfExpectRho
            ,getFree,getFreePredL,unionTwo,subPred,subpairs,disp0,lv,subst
            ,boolT,unitT,tlist,tpair,tunit',tsum,tcode,ioT,arrow,applyT,applyT',listT
            ,pairT,arrowT,kind4Atom,atomT,sumT,notEqKind,notEqT,propT,intT,charT
            ,ptsub,karr,chrSeqT,symbolT,floatT,ttag,tlabel,tarr,tagT
            ,stringT,equalKind,infixEqName,tvsTau,subPairs,teq,equalityP,pred2Tau
            ,argsToEnv,binaryLift,expecting,bindtype,failtype,returntype,zap,rootT,rootTau
            ,exhibitL,exhibitTT,apply_mutVarSolve_ToSomeEqPreds
            ,parsePT,mutVarSolve,compose,o,composeTwo,equalRel,parseIntThenType,parseType,showPred
            ,prune,pprint,readName,exhibit2,injectA, showKinds,showKinds2, showKinds3
            ,subtermsTau,subtermsSigma,kindOfM,extToTpatLift)
import SyntaxExt(SynExt(..),Extension(..),synKey,synName,extKey,buildExt,listx,pairx,natx)
import List((\\),partition,sort,sortBy,nub,union,unionBy
           ,find,deleteFirstsBy,groupBy,intersect)
import Encoding2
import Auxillary(plist,plistf,Loc(..),report,foldrM,foldlM,extend,extendL,backspace,prefix
                ,DispInfo(..),Display(..),newDI,dispL,disp2,disp3,disp4,tryDisplay
                ,DispElem(..),displays,ifM,anyM,allM,maybeM,eitherM,dv,dle,dmany,ns)
import LangEval(vals,env0,Prefix(..),elaborate)
import ParserDef(pCommand,parseString,Command(..),getExp,parse2, program,pd)
import Char(isAlpha,isUpper)
import System.IO.Unsafe(unsafePerformIO)
import SCC(topSortR)
import Cooper(Formula(TrueF,FalseF),Fol,Term,toFormula,integer_qelim,Formula)

import qualified Data.Map as Map
   -- (Map,empty,member,insertWith,union,fromList,toList,lookup)

import NarrowData(DefTree(..),NName(..),Rule(..),Prob(..),NResult(..),Rel(..)
                 ,andR,andP,andf,freshX,dProb)
import Narrow(narr,defTree,Check(..),matches)
import Value(Label(..),Equal(..))

------------------------------------------------------------
-- In order to instantiate the narrowing code we must supply
-- several functions that interact with the type-checking
-- monad. This is done by supplying the following instance.

instance Check (Mtc TcEnv Pred) where
  getMode s = getM s False
  wait = waitN  -- warnM [Ds "<return> to continue ..."] >> fio2Mtc(fio (getLine))
  rewNestedEqual (t1,t2) =
    do { rs <- getLemmaRules "Equal";
       ; env <- tcEnv
       ; truths <- getTruths
       ; normWithLemmas (rules env,tyfuns env,truths) rs (teq t1 t2)
       -- ; applyLemmas rs (teq t1 t2)
       }
  getDefTree (NTyCon s sx lev _) =
    do { info <- defTreeInfo s
       ; case info of
           Just(nm,tree) -> return tree
           Nothing -> failM 0 [Ds "1) Unknown type function: ",Ds s] }
  getDefTree other = failM 1 [Ds "Bad type function: ",Dd ( other)]
  tryRewriting t =
    do { (t2,u, newtruths) <- liftNf norm2Tau t
       ; if t==t2 then return Nothing else return (Just (t2,u))};
  rewEq (t1 @(TyFun nm k xs),t2) =
            do {rs <- getLemmaRules nm; try True (t1,t2) rs}
    where try True (t1,t2@(TyFun nm k xs)) [] =
            do { rs <- getLemmaRules nm; try False (t2,t1) rs }
          try other (t1,t2) [] = return Nothing
          try other (t1,t2) ((lemma,(commutes,vs,[],lhs,rhs)):more) =
            case match2 ([],[]) [(lhs,t1),(rhs,t2)] of
              Just u -> do { warnM [Ds ("\n*** Trying equality lemma '"++rname lemma)
                                  ,Ds "' on term:\n   ",Dd (teq t1 t2)]
                           ; return (Just ([],[]))} -- matching means no variables escape
              Nothing -> try other (t1,t2) more
          try other (t1,t2) (m:more) = try other (t1,t2) more
  rewEq (_,_) = return Nothing
  normalizeTau t = do { (ans,u,_) <- liftNf norm2Tau t; return (ans,u)}



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
   solveSomeEqs p preds = do { env <- tcEnv; (u,ps,_,_) <- solveConstraints p env preds; return(ps,u)}
   show_emit = getMode "predicate_emission"
   getTruths = getAssume
   setTruths = setAssumptions
   currentLoc = getLoc
   syntaxInfo = getSyntax
   normTyFun = normTyFunTau
   fromIO = io2Mtc
   getIoMode = getMode

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
collectPred x = 
  do { (ans,ps) <- extractAccum x
     ; ps2 <- zonk ps
     ; return(ans,ps2) }

getMatchingRules p s = do { env <- tcEnv; return(filter p (getRules s env))}

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
  = TcEnv { var_env :: FiniteMap Var (PolyKind,Mod,CodeLevel,Exp) -- Term Vars
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
          , sourceFiles :: [String]
          , syntaxExt :: [SynExt String]
          }

tcEnv0 = unsafePerformIO(runFIO (decMany preDefDec initEnv) errF)
  where initEnv = TcEnv Map.empty toEnvX [] 0 Z [] [] Map.empty Map.empty env0 [] [] [] [listx,pairx,natx]
        errF loc n s = error ("While initializing "++show loc++"\n"++s)

typeConstrEnv0 = type_env tcEnv0
initTcEnv = addFrag frag0 tcEnv0

frag0 = Frag (map f vals) [] [] [] [] [] []
  where f (nm,maker) = g (nm,maker nm)
        g (nm,(v,sigma)) = (Global nm,(K [] sigma,Rig,0,Var (Global nm)),LetBnd)

-- Used for adding simple Frags, where we don't expect things like theorems etc.
addFrag (Frag pairs rigid tenv eqs theta rs exts) env =
   env { var_env = addListToFM (var_env env) (map projBindMode pairs)
       , generics = foldr acc (generics env) pairs
       , type_env = tenv ++ (type_env env)
       , bindings = bindingsNew
       , assumptions = union (union eqs (map (uncurry Equality) eqsNew)) (subPred theta (assumptions env))
       , rules = appendFMmany (rules env) rs
       , syntaxExt = (syntaxExt env) ++ exts
       }
 where acc (x,(K lvs rho,mod,lev,exp),LamBnd) xs = (x,rho):xs
       acc (x,(rho,mod,lev,exp),LetBnd) xs = xs
       (bindingsNew,eqsNew) = extendref theta (bindings env)

addFragC name (frag@(Frag pairs rigid tenv eqs theta rs exts)) env =
 do { let (bindingsNew,eqs2) = extendref theta (bindings env)
    ; preds <- failIfInConsistent name (bindings env) theta eqs2
    ; (theta',eqs') <- refine bindingsNew
                              (union (union eqs preds) (subPred theta (assumptions env))) rs
    ; return(env { var_env = addListToFM (var_env env) (map projBindMode pairs)
                  , generics = let acc (x,(K lvs rho,mod,lev,exp),LamBnd) xs = (x,rho):xs
                                   acc (x,(K lvs rho,mod,lev,exp),LetBnd) xs = xs
                               in foldr acc (generics env) pairs
                  , type_env = tenv ++ (type_env env)
                  , bindings = theta'
                  , assumptions = eqs'
                  , rules = appendFMmany (rules env) rs
                  , syntaxExt = (syntaxExt env) ++ exts
                  })}


letExtend :: String -> Frag -> TC a -> TC a
letExtend name frag comp =
  do { env <- tcEnv
     ; env2 <- addFragC name (markLet frag) env
     ; inEnv env2 comp }

lambdaExtend :: String -> Frag -> TC a -> TC a
lambdaExtend name frag comp =
  do { env <- tcEnv
     ; env2 <- addFragC name (markLambda frag) env
     ; inEnv env2 comp }

underRules rs computation =
  do { env <- tcEnv
     ; inEnv (env{rules = appendFMmany (rules env) rs}) computation}

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
  ,("predicate_emission",False,"Reports the fact that a predicate has been emitted. Predicates are collected at generalization sites, and are either solved, or abstracted into constrained types.")
  ,("narrowing",False,"Shows the steps taken when narrowing. Useful for debugging when narrowing does not return the result desired.")
  ,("theorem",False,"Reports when a lemma is added by a 'theorem' declaration, and when such a lemma is applicable.")
  ,("kind",False,"Displays kinds of subterms when using the :k or :t commands.")
  ,("unreachable",False,"Displays information when checking for unreachable clauses.")
  ,("verbose",False,"For Debugging the compiler")
  ]

mode0 = map (\ (name,value,doc) -> (name,value)) modes_and_doc

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

data BindMode = LamBnd | LetBnd

projBindMode (var,quad,mode) = (var,quad)

-- type ToEnv = [(String,Tau,PolyKind)] -- In RankN.hs
data Frag = Frag [(Var,(PolyKind,Mod,CodeLevel,Exp),BindMode)] [TcTv] ToEnv
                 [Pred] Unifier [(String,(RWrule))]
                 [SynExt String]

interesting (Frag env skols _ eqn theta rules exts) = not(null eqn)

nullFrag = Frag [] [] [] [] [] [] []

markLet  (Frag xs ys zs eqs theta rs exts) = Frag (map f xs) ys zs eqs theta rs exts
  where f (var,quad,_) = (var,quad,LetBnd)

markLambda  (Frag xs ys zs eqs theta rs exts) = Frag (map f xs) ys zs eqs theta rs exts
  where f (var,quad,_) = (var,quad,LamBnd)

-- One can perform substitution and zonking on Frags

instance Zonk (Mtc TcEnv Pred) Frag where
  zonkG (Frag xs ys zs eqs theta rs exts) =
    do { xs2 <- mapM f1 xs
       ; eqs2 <- mapM zonkG eqs
       ; rs2 <- mapM zonkG rs
       ; theta2 <- zonkG theta
       ; return(Frag xs2 ys zs eqs2 theta2 rs2 exts)}
   where f1 (x,(y,mod,z,w),mode) = do { y' <- zonkG y; return(x,(y',mod,z,w),mode)}
  tvs f = error "No way to get the type vars from a Frag"
  
instance TypeLike (Mtc TcEnv Pred) Frag where
  sub env (Frag xs ys zs eqs theta rs exts) =
     do { xs' <- mapM f xs;
        ; eqs2 <- sub env eqs
        ; zs' <- mapM g zs
        ; rs2 <- mapM (sub env) rs
        ; theta2 <- composeM env theta
        ; return(Frag xs' ys zs' eqs2 theta2 rs2 exts)}
    where f (v,(s,mod,lev,exp),mode) = do { s2 <- sub env s; return(v,(s2,mod,lev,exp),mode)}
          g (str,tau,kind) =
            do { t2 <- sub env tau; k2 <- sub env kind; return(str,t2,k2)}

composeM (env@(_,s1,_,_)) s2 =
 do { let f (v,t) = do { t2 <- sub env t; return(v,t2) }
    ; prefix <- mapM f s2
    ; return(prefix ++ s1)}

infixr +++    --- NOTE (+++) is NOT COMMUTATIVE, see composeU
(Frag xs ys zs eqs u1 rs1 exts1) +++ (Frag as bs cs eqs2 u2 rs2 exts2) =
  eitherM (mergeMgu u1 u2)
    (\ u3 -> return (Frag (xs++as) (ys++bs) (zs++cs) (union eqs eqs2) u3 (rs1++rs2) (exts1++exts2)))
    (\ (mess,t1,t2) -> failD 2 [Ds "Inconsistent types checking patterns: "
                               ,Dd t1,Ds " != ", Dd t2])

composeU s1 s2 = ([(u,subTau s1 t) | (u,t) <- s2] ++ s1)

-- adding things to Frags

addPred :: [Pred] -> Frag -> Frag
addPred truths (Frag xs ys zs eqs theta rs exts) = (Frag xs ys zs (union truths eqs) theta rs exts)

addEqs ps (Frag terms pvs types eqs theta rules exts)  =
          (Frag terms pvs types (subPred theta (ps ++ eqs)) theta rules exts)


addSkol :: [TcTv] -> Frag -> Frag
addSkol vs (Frag xs ys zs eqs theta rs exts) = Frag xs (vs++ys) zs eqs theta rs exts

addTermVar p@(v,(K _ (Forall(Nil ([],Rtau tau))),m,l,e),mode)
           frag@(Frag terms pvs types eqs theta rules exts) =
   ifM (isProp Nothing tau)
       (return (addEqs [(Rel tau)] (Frag (p:terms) pvs types eqs theta rules exts)))
       (return (Frag (p:terms) pvs types eqs theta rules exts))
addTermVar p (Frag terms pvs types eqs theta rules exts) =
       (return (Frag (p:terms) pvs types eqs theta rules exts))

addUnifier u (Frag terms pvs types eqs theta rules exts) =
   eitherM (mergeMgu u theta)
      (\ u2 -> return(Frag terms pvs types eqs u2 rules exts))
      ( \ (s,t1,t2) -> failD 2 [Ds "Inconsistent types checking patterns: "
                               ,Dd t1,Ds " != ", Dd t2])

addPVS vs (Frag terms pvs types eqs theta rules exts) =
          (Frag terms (vs++pvs) types eqs theta rules exts)

addRules rs (Frag terms pvs types eqs theta rules exts) =
            (Frag terms pvs types eqs theta (rs ++ rules) exts)

-- using Frags

applyTheta Rig (Frag terms pvs types eqs theta rules exts) term = sub ([],theta,[],[]) term
applyTheta Wob frag term = return term

appTheta Rig theta term = sub ([],theta,[],[]) term
appTheta Wob theta term = return term

-- extracting elements of a Frag

getToEnv (Frag terms pvs types eqs theta rules exts) = types
getTermVars (Frag terms pvs types eqs theta rules exts) = map fst terms
  where fst (name,quad,mode) = name
getTheta (Frag terms pvs types eqs theta rules exts) = theta
getEqs (Frag terms pvs types eqs theta rules exts) = eqs
skolFrag (Frag _ skolvars _ _ _ _ _) = skolvars
fragRules (Frag terms pvs types eqs theta rules exts) = rules

showFrag message frag =
  do { (Frag xs rs tenv eqs theta rules exts) <- zonk frag
     ; outputString ("\n********** Frag ***************" ++ message ++
           "\nBindings = "++plistf showBind "" (take 5 xs) ", " ""++
           "\nSkolem = "++show rs++
           "\nRefinement = "++ show theta++
           "\nAssumptions = "++showPred eqs++"\n*********************") }


dispTcTv (x@(Tv unq flav k)) = [Dd x,Ds ": ",Dd k]

dispFrag message frag =
   do { (Frag xs rs tenv eqs theta rules exts) <- zonk frag
      ; warnM [Ds ("\n********** Frag ***************" ++ message)
                ,Ds "\n   Bindings = ",Dlf dispBind (take 5 xs) "\n              "
                ,Ds "\n     Skolem = ",dle dispTcTv rs ", "
                ,Ds "\n Refinement = ",Dl theta ", "
                ,Ds "\nAssumptions = ", Dl eqs "; "
                ,Ds "\n   Theorems = ",Dl (map snd rules) "; "]}

showBind (x,(t,mod,_,_),mode) = show x ++":"++show t
dispBind d (x,(t,mod,_,_),mode) = displays d [Dd x,Ds ":",Dd t]

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
getLemmas = do { ts <- getAllTheorems; return(filter isRewrite ts)}


getTCEnv :: TC (FiniteMap Var (PolyKind,Mod,CodeLevel,Exp))
getTCEnv = Tc (\ env -> return (var_env env,[]))

getGenerics :: TC [(Var,Sigma)]
getGenerics = Tc (\ env -> return (generics env,[]))

getLevel :: TC Int
getLevel = Tc (\ env -> return (level env,[]))

getSyntax :: TC [SynExt String]
getSyntax = Tc (\ env -> return (syntaxExt env,[]))

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

getVar :: Var -> TcEnv -> Maybe(PolyKind,Mod,CodeLevel,Exp)
getVar nm env = Map.lookup nm (var_env env)
    
getRules :: String -> TcEnv -> [(RWrule)]
getRules "" env = concat (map snd (Map.toList (rules env)))
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
-- "Simple Unification-based Type Inference for GADTs" by Simon
-- Peyton Jones, Stephanie Weirich, and Dimitrios Vytiniotis

instance Typable (Mtc TcEnv Pred) Exp Rho where
  tc = typeExp Wob

inferExp :: Exp -> TC(Rho,Exp)
inferExp = infer

typeExp :: Mod -> Exp -> Expected Rho -> TC Exp
typeExp mod (Lit x) expect = do { x' <- tc x expect; return (Lit x') }
typeExp mod (Var v) expectRho =
     do { m <- getLevel
        ; (polyk,mod,n,exp) <- lookupVar v
        ; when (n > m) (failD 2 [Ds (show v++" used at level "++show m++" but defined at level "++show n)])
        ; when False -- (show v=="f99") -- False
            (do { truths <- getTruths
                ; showKinds (varsOfPair varsOfPoly varsOfExpectRho) (polyk,expectRho)

                ; warnM [Ds ("\nChecking variable "++show v)
                        ,Ds "\nSigma = ",Dd polyk
                        ,Ds "\nExpect = ", Dd expectRho
                        ,Ds "\nTruths = ",Dl truths ", "
                        ,Ds "\nmod = ",Dd mod]
                ; return ()})

        ; handleM 2 (morepoly (show (Var v)) polyk expectRho) (resulterr (Var v) polyk expectRho)
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
        ; x <- handleM 2 (check arg arg_ty) (badarg e arg arg_ty)
        ; zz <- zonk arg_ty
        ; fz <- zonk fun_ty
        ; ww <- zonk res_ty
        ; d <- getDisplay
        {-
        ; whenM False --(show arg == "ex1")
            [Ds ("\nChecking application: "++show e)
            ,Ds "\nfun type = ",Dd fun_ty
            ,Ds "\nzonked fun type = ",Dd fz
            ,Ds "\narg type = ",Dd zz
            ,Ds "\nresult type = ",Dd ww
            ,Ds "\n expected type = ",Dd expect]
        -}
        ; ns4 <- morePoly e res_ty expect
        ; return(App f x) }
typeExp mod (exp@(Lam ps e _)) (Check t) =
     do { (frag,ps2,ts,result) <- checkBndrs localRename mod nullFrag ps t
        ; e2 <- underFrag (show ps,result) (markLambda frag) (typeExp mod e (Check result))
        ; escapeCheck exp t frag
        ; return(Lam ps2 e2 []) }
typeExp mod (exp@(Lam ps e _)) (Infer ref) =
     do { (ts2,frag,ps2) <- inferBndrs localRename nullFrag ps
        ; (t,e2) <-  underFrag (show ps,starR) (markLambda  frag) (infer e)
        -- ESCAPE CHECK
        ; escapeCheck exp t frag
        ; writeRef ref (foldr arrow t ts2)
        ; return(Lam ps2 e2 []) }
typeExp mod term@(Ann body pt) exp_ty =
     do { loc <- getLoc
        ; (ann_ty,_) <- checkPT (show body) loc pt
        ; exp <- check body ann_ty
        ; morePoly term ann_ty exp_ty
        ; return (Ann exp pt) }
typeExp mod (Let ds e) expect =
     do { (frag,ds2) <- inferBndrForDecs "let" localRename ds
        ; let pickRho (Check r) = r
              pickRho (Infer _) = starR
              message = bindingGroupNames "let" ds
        ; e2 <- underFrag (message,pickRho expect) (markLet frag) (typeExp mod e expect)
        ; return(Let ds2 e2)}
typeExp mod (Circ vs e ds) expect = tcCircuit vs e ds expect
typeExp mod (Case exp ms) (Check rng) =
     do { dom <- newTau star
        ; (e2,oblig) <- peek (typeExp Wob exp (Check(Rtau dom)))
        ; dom2 <- zonk dom
        ; ms2 <- checkL oblig mod ms dom2 rng
        ; return(Case e2 ms2) }
typeExp mod (Case exp ms) (Infer ref) =
     do { rng <- newRho star
        ; ((domain,e2),oblig) <- peek (infer exp)
        ; dom <- case domain of
                  Rtau d -> return d
                  x -> failM 3 [Ds "Inferring the type of ",Dd (Case exp ms)
                               ,Ds " returns Rho type: ",Dd x]
        ; ms2 <- checkL oblig mod ms dom rng
        ; writeRef ref rng
        ; return(Case e2 ms2) }
typeExp mod s@(Do ss) expect =
      do { (m,b) <- unifyMonad expect
         ; (K _ bindSig,bmod,bn,bexp) <- lookupVar (Global "bind")
         ; (K _ failSig,fmod,fn,fexp) <- lookupVar (Global "fail")
         ; bindt <- bindtype m
         ; failt <- failtype m
         ; morepoly "bind" bindSig bindt
         ; morepoly "fail" failSig failt
         ; ss2 <- tcStmts mod m b ss
         ; return(Do ss2)}
typeExp mod (CheckT e) expect =
     do { ts <- getBindings
        ; refinement <- zonk ts
        ; assumptions <- getAssume
        ; (ass2,_,_) <- nfPredL assumptions
        ; rules <- getAllTheorems

        ; typ <- zonk expect
        ; warnM [Ds ("\n\n*** Checking: " ++ (take 62 (show e)))
                ,Ds "\n*** expected type: ",Dd typ
                ,Dwrap 80 "***    refinement: " refinement ", "
                ,Dwrap 80 "***   assumptions: " ass2 ", "
                ,Dwrap 80 "***      theorems: " (map ruleName(filter (not . axiom) rules)) ","]
        ; env <- tcEnv
        ; checkLoop typ env
        ; x <- typeExp mod e expect
        ; return(CheckT x)}
typeExp mod (Lazy e) expect = do { x <- typeExp mod e expect; return(Lazy x)}
typeExp mod (Exists e) (Check (tt@(Rtau (TyEx xs)))) =
     do { (vs,preds,tau) <- instanL [] xs  -- ## WHAT DO WE DO WITH THE PREDS?
        ; x <- typeExp mod e (Check (Rtau tau))
        ; return(Exists x)}
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
typeExp mod (ExtE x) expect =
  do { exts <- getSyntax
     ; loc <- getLoc
     ; let lift0 nm = Var (Global nm)
           lift1 nm x = App (lift0 nm) x
           lift2 nm x y = App (lift1 nm x) y
           lift3 nm x y z = App (lift2 nm x y) z
     ; new <- buildExt (show loc) (lift0,lift1,lift2,lift3) x exts
     ; typeExp mod new expect
     }



--------------------------------------------------------------------
-- Functions to report reasonably readable  errors

notfun e fun_ty s =
   failK "notfun" 2 [Ds "\nIn the expression: "
                ,Dd e
                ,Ds "\nthe function has a non-functional type: "
                ,Dd fun_ty]

badarg :: Exp -> Exp -> Sigma -> String -> TC Exp
badarg all arg arg_ty s =
 do { z <- zonk arg_ty
    --; (computed::Rho,_) <- infer arg
    ; failK "badarg" 2
       [Ds "\nIn the expression\n"
       ,Dd all
       ,Ds "\nthe argument:\n"
       ,Dd arg
       ,Ds "\ndid not have type: "
       ,Dn arg_ty
      -- ,Ds "\nInstead, it had type:\n"
      -- ,Dd computed
       ,Ds s]}

resulterr e res_ty expect s =
  do { ex <- case expect of {Check t -> return t; Infer ref -> readRef ref }
     ; rt <- zonk res_ty
     ; ex2 <- zonk ex
     ; kindelements <- showKinds2 (rt,ex)
     ; refinement <- getBindings
     ; truths <- getTruths
     ; failK "resulterr" 2
         [Ds "\nIn the expression: "
         ,Dn e
         ,Ds "the result type: "
         ,Dn rt
         ,Ds "was not what was expected: "
         ,Dn ex
         ,Dr kindelements
         --,Ds "refinement: ",Dl refinement ", "
         ,Ds "\ntruths:\n  ",Dl truths "\n  "
         ,Ds ("\n"++s)
         -- ,Ds ("\n"++(shtt rt)++" =/= "++shtt ex)
         ]}

{-
morePoly::(Show a,Exhibit (DispInfo Z) a,Exhibit (DispInfo Z) b
          ,Exhibit (DispInfo Z) c,Subsumption m b(Expected c)
          ,TypeLike m b,TypeLike m c)
          => a -> b -> Expected c -> m ()
-}

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
        do { (t1,_) <- checkPT s1 Z a
           ; (t2,_) <- checkPT s2 Z b
           ; b <- morepoly "test" t1 t2; outputString (show b ++ "\n") }
    (a@(Forallx All xs _ x),y) ->
        do { (t1,_) <- checkPT s1 Z a
           ; t2 <- toRho (typeConstrEnv0,Z,[],[]) y
           ; b <- morepoly "test"  t1 t2; outputString (show b ++ "\n") }
    (x,y) ->
        do { t1 <- toRho (typeConstrEnv0,Z,[],[]) x
           ; t2 <- toRho (typeConstrEnv0,Z,[],[]) y
           ; b <- morepoly "test"  t1 t2; outputString (show b ++ "\n") }) :: TC ())

--------------------------------------------------------------
-- fun Matches are Typeable  (Match [Pat] Exp Dec)
-- This instance useable for (Fun matches)
-- f :: d1 -> d2 -> rng
-- f p1 p2 = e    leads to a call like:
-- tc (line 1, [p1,p2],Normal e,[]) (Check (d1 -> d2 -> rng))

instance Typable (Mtc TcEnv Pred) (String,Loc,[Pat],Body Exp,[Dec]) Rho where
  tc = typeMatchPs Wob

fragForPs mod nm loc expectedTy pats whereDs = newLoc loc $
  do { (patFrag,ps1,ts,rng) <- checkBndrs localRename mod nullFrag pats expectedTy
     ; let message = bindingGroupNames "a where clause that binds" whereDs
           name [p] = "the pattern "++show p
           name ps = plist "the patterns " ps " " " "
     ; (declFrag,ds2) <- underFrag (name pats,starR) (markLambda patFrag)
                                   (inferBndrForDecs message localRename whereDs)
     ; bodyFrag <- (markLet declFrag +++ markLambda patFrag)
     ; return(bodyFrag,ps1,ts,(patFrag,rng,ds2))}

typeMatchPs:: Mod -> (String,Loc,[Pat],Body Exp,[Dec]) -> Expected Rho -> TC(String,Loc,[Pat],Body Exp,[Dec])
typeMatchPs mod (x@(nm,loc,ps,Unreachable,ds)) (Check t) = newLoc loc $
    (do -- ts <- getTruths
        -- bs <- getBindings
        verbose <- getMode "unreachable"
        whenM verbose [Ds "\n\nChecking the unreachability of the clause:\n",Ds (nm++" "),Dl ps " ",Ds " = unreachable\n"]
        checkUnreachable (fragForPs mod nm loc t ps ds) 
                         (\ message -> whenM verbose [Ds message,Ds "\nUnreachability confirmed."] >> return x))
typeMatchPs mod (nm,loc,ps,body,ds) (Check t) = newLoc loc $
     do { -- warnM [Ds ("\nBEFORE fragForPs "++nm)];
         (bodyFrag,ps1,ts,(patFrag,rng,ds2)) <- fragForPs mod nm loc t ps ds
        --;  warnM [Ds ("\nAfter fragForPs "++nm)]
        ; let err s  =
               (do { (Frag zs _ _ ts theta rs exts) <- zonk patFrag
                   ; truths <- getBindings
                   ; failK "tcMatch[Pat]" 3
                       [Ds "\n*** Error in clause: "
                       ,Dl ps " ",Ds " = ",Ds (show body), Ds ":\n    ",Dd t
                       ,Ds "\n*** with\n   ",Dlf dispBind zs ", "
                       ,Ds "\n*** where ", Dl (subPred truths ts) ", "
                       ,Ds s]} )
        ; let context = mContxt loc nm ps body
        ; let comp theta = do { rng2 <- appTheta mod theta rng
                              ; ans <- chBody1 mod patFrag body rng2
                              ; return ans
                              }
        ; body3 <- handleM 2 (underFragUsingTheta (context,rng) bodyFrag comp) err

        ; escapeCheck body t patFrag
        ; return(nm,loc,ps1,body3,ds2) }

typeMatchPs mod (nm,loc,ps,body,ds) (Infer ref) = newLoc loc $
     do { (ts,frag0,ps1) <- inferBndrs localRename nullFrag ps

        ; let patFrag = markLambda frag0
              message = bindingGroupNames "a where clause that binds" ds
              name = plist "the patterns " ps " " " "

        ; (declFrag,ds2) <- underFrag (name,starR) patFrag
                                      (inferBndrForDecs message localRename ds)
        ; bodyFrag <- (markLet declFrag +++ patFrag)
        ; (rng,body3) <- underFrag (matchContext ps body,starR) bodyFrag (infer body)
        -- ESCAPE CHECK
        ; escapeCheck body rng patFrag
        ; writeRef ref (foldr arrow rng ts)
        ; return(nm,loc,ps1,body3,ds2) }

matchContext ps body = bodyName (Pvar (Global ("match: "++show ps))) body

-- Contexts are passed as the 1st argument to "under". They
-- are a String and are used in error messages. We compute legible ones here.

mContxt loc nm ps body = -- "\n"++show loc++"\n"++
     nm++plist " " ps " " " = "++ lhs ++ dots
  where bodyString = (show body)
        lhs = take 20 bodyString
        dots = if length bodyString > 20 then " ... " else " "


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
-- Bodies are Typable

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
typeBody mod Unreachable expect = failD 3 [Ds "No Unreachable Yet 1"]

-----------------------------------------------------------
-- (Case matches) are Typeable
-- case e of { (C p1 p2) -> e }    leads to a call like
-- tc (line 1,(C p1 p2),Normal e,[]) expected

predicateToProblem (Rel x) = TermP x
predicateToProblem (TagNotEqual t u) = EqP(t,u) -- negate problem! FISHY TODO
predicateToProblem (Equality x y) = EqP(x,y)

predsToProb [] ans = andP ans
predsToProb (p:ps) ans = predsToProb ps (predicateToProblem p : ans)

freshenVs term =
   do { (vs,_) <- get_tvs term
      ; let new (v@(Tv un (Rigid _ _ _) k)) xs =
                do {t <- newTau k; return((v,t):xs)}
            new v xs = return xs
      ; mapping <- foldrM new [] vs
      ; freshTerm <- sub ([],mapping,[],[]) term
      ; return(mapping,freshTerm)}


----------------------------------------------------------------
-- Here we WANT something to go wrong! Either "computation"
-- raises a "bad refinement" error, or there is some non-null
-- set of equations (which we get to assume is true) which is non-satisfiable.
-- To check non-satisfiable, put the term in normal form, then
-- replace the Rigid vars with fresh ones and narrow.
-- If this leads to Zero possible solutions, without running out
-- of resources, it is non-satisfiable.

checkUnreachable computation good = handleK (=="bad refinement") 3
  (do { (frag,ps,ts,_) <- computation
      ; let comp = do {(pred0,_,_) <- nfPredL (getEqs frag); return pred0}
      ; preds <- underRules (fragRules frag) comp
      ; let problem = predsToProb preds []
      ; (mapping,prob2) <- freshenVs problem
      -- ; dispFrag "Frag in unreachable = " frag
      -- ; warnM [Ds "preds = ", Dd preds]
      ; let bad = doNotGuardUnreachable (getTheta frag `o` mapping) preds (zip ps ts)
      ; verbose <- getMode "unreachable"
      ; whenM verbose [Ds "Checking satisfiabilty of the predicates:\n   ",Dl preds "\n   "]
      ; existsNonSat preds prob2 good bad}) good

existsNonSat [] prob2 good bad = bad 0 []
existsNonSat (p:ps) prob2 good bad =
  do { d2 <- getDisplay
     ; ans <- narr "unreachable" (25,1,d2,False) [(prob2,andR[],([],[]))] []
     ; case ans of
         ([]    ,(_,_,_,False)) -> good "Narrowing finds non-satisfiable problem."
         ([]    ,(_,_,_,True))          -> bad 1 []
         (((_,_,(_,sub)):xs),(_,_,_,True))  -> bad 2 sub
         (((_,_,(_,sub)):xs),(_,_,_,False)) -> bad 2 sub}

doNotGuardUnreachable map prob2 pairs 0 _ =
  failM 2 [Ds "\nThe patterns:\n  ",Dlf f34 pairs " ",Ds "\ndo not guard unreachable code. "
          ,Ds "If the code was unreachable,\nthen there would be some set of"
          ,Ds " assumptions that was unsatisfiable.\nThis is not the case, since"
          ,Ds " the set of assumptions is empty."
          ,Ds "Map = ", Dl map "; "]
doNotGuardUnreachable map prob2 pairs 1 _ =
  failM 2 [Ds "\nI cannot prove that the patterns:\n  ",Dlf f34 pairs " ",Ds "\nguard unreachable code. "
          ,Ds "I ran out of narrowing resources while\nattempting to prove that the problems:\n  "
          ,Dl prob2 "\n  ",Ds "\nare not satisfiable. Perhaps a theorem or lemma might help?"]
doNotGuardUnreachable map prob2 pairs 2 sub =
  failM 2 [Ds "\nThe patterns:\n  ",Dlf f34 pairs " ",Ds "\nguard REACHABLE code. "
          ,Ds "If the code was unreachable, then the problems:\n  ",Dl prob2 "\n  "
          ,Ds "\nwould not be satisfiable, but under the refinement: "
          ,Dl (invertRefinement map sub) ", "
          ,Ds "\nthey are shown to be true."]

-- helpers to print things nicely.

f34 d (pat,sig) = displays d [Ds "(",Dd pat,Ds ": ",Dd sig,Ds ")"]

invertRefinement mapping [] = []
invertRefinement mapping ((v,t):xs) = fix mapping : invertRefinement mapping xs
  where fix [] = (v,t)
        fix ((x,TcTv y):more) | y==v = (x,t)
        fix (_:more) = fix more

----------------------------------------------------------------

fragForMatch caseOblig mod expectedTy pat whereDs =
  do { (dom,rng) <- (unifyFun expectedTy)
     ; (frag0,p1) <- checkBndr localRename mod nullFrag dom pat
                     -- Could raise "bad_refinement"
     ; frag1 <- zonk(markLambda (addEqs caseOblig frag0))
     ; let message = bindingGroupNames "a where clause that binds" whereDs

     --; warnM [Ds "\nCase Oblig = ",Dd caseOblig]
     --; dispFrag ("Frag for Casematch: "++ show pat) frag1
     ; (frag2,ds2) <- underFrag (show pat,starR) frag1
                                (inferBndrForDecs message localRename whereDs)
     ; bodyFrag <- (markLet frag2 +++ frag1)
     ; return (bodyFrag,[p1],[dom],(frag1,rng,ds2))
     }

typeMatch:: [Pred] -> Mod -> Match Pat Exp Dec -> Expected Rho -> TC (Match Pat Exp Dec)
typeMatch caseOblig mod (x@(loc,p,Unreachable,ds)) (Check t) =
  do { verbose <- getMode "unreachable"
     ; whenM verbose [Ds "\n\nChecking unreachability of the case clause:\n",Dd p, Ds " -> unreachable\n"]
     ; checkUnreachable (fragForMatch caseOblig mod t p ds)
                        (\ message -> whenM verbose [Ds message,Ds "\nUnreachability confirmed."] >>return x)
     }

typeMatch caseOblig mod (loc,p,body,ds) (Check t) = newLoc loc $
  do { (bodyFrag,[p1],_,(argFrag,rng,ds2)) <- fragForMatch caseOblig mod t p ds
     ; let err s  = 
               (do { let (Frag zs _ _ truths theta rs exts) = bodyFrag
                   ; binds <- getBindings
                   ; typeString <- renderRho t
                   ; failK "tcMatchPat" 2
                      [Ds ("\n*** Error type checking match at "++show loc++" ***\n")
                      ,Ds ("\n"++render((ppPat p)<+>(text "->")$$ PP.nest 3 (ppBody body)))
                      ,Ds  "\n\n***   type:\n",Ds typeString
                      ,Ds  "\n\n***   vars:\n   ",Dlf dispBind zs "\n   "
                      ,Dwrap 80 "*** truths: " (subPred binds truths) ", "
                      ,Ds ("\n"++s)]})
     -- check the clause
     ; let comp theta = do { range <- appTheta mod theta rng
                           ; typeBody mod body (Check range) }
     ; body3 <- handleK (\ x -> (prefix "Not in scope" x)) 4 
                (underFragUsingTheta (bodyName p body,rng) bodyFrag comp) err
     ; escapeCheck body t argFrag
     ; return(loc,p1,body3,ds2) }
typeMatch caseOblig mod (loc,p,body,ds) (Infer ref) = newLoc loc $
  do { (dom,frag0,p1) <- inferBndr localRename nullFrag p
     ; let frag1 = markLambda frag0
           message = bindingGroupNames "a where clause that binds" ds
     ; (frag2,ds2) <- underFrag (message,starR) frag1 (inferBndrForDecs message localRename ds)
     ; bodyFrag <- (markLet frag2 +++ frag1)
     ; (rng,body3) <- underFrag (bodyName p body,starR) bodyFrag (infer body)
     -- ESCAPE CHECK
     ; escapeCheck body rng frag1
     ; writeRef ref (arrow dom rng)
     ; return(loc,p1,body3,ds2) }

--------------------------------------------------------------------
-- Patterns are Typeable
-- Usually we want Pat in the class TypeableBinder. But, for 1st class
-- patterns we need both. E.g. a declaration like:    pattern LHS = RHS
-- pattern If x y z = Case x [(True,y),(False z)]
-- where we need to check that the pattern on the RHS is well formed
-- when using the variables defined on the LHS.

instance Typable (Mtc TcEnv Pred) Pat Rho where
  tc (Plit l) expect = do { l2 <- tc l expect; return(Plit l2) }
  tc (Pvar v) expect =
     do { (polyk,mod,n,Var u) <- lookupVar v
        ; handleM 2 (morepoly (show (Pvar v)) polyk expect) (resulterr (Pvar v) polyk expect)
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
     do { (polyk,mod,n,exp) <- lookupVar c
        ; loc <- getLoc
        ; (rigid,assump,rho) <- instanPatConstr (arisesPat p) Ex loc (show p) polyk
        ; ps2 <- checkArgs ps rho expect
        ; return (Pcon c ps2)
        }
  tc p expect = failD 2 [Ds "Bad pattern on RHS of pattern decl: ",Dd p]


--------------------------------------------------------------
---------------------------------------------------------------------
-- Suppose we have the following where
--   1) (n:: Nat' _m) where _m is rigid
--   2) halve:: Nat' {plus x x} -> Nat x
--
-- case check halve (S (S n)) of
--     Z -> unreachable
--     (S Z) -> check R(Pad(One Z))
--
-- since n:(Nat' _m) is rigid, one would expect the type of (S (S n))
-- and the type of (halve (S (S n))) to be rigid. Unfortunately
-- we get:  (halve (S (S n))) :: Nat f   WHEN (Equal {plus f f} _m)
-- To deal with this when we check the type of a case object for
-- rigidity, we must also rigidify any free type variables that
-- appear free in one side of an Equal obligation that are equated
-- to a rigid type in the other side. I.e.(Equal {plus f f} _m).
-- Note f appears free in {plus f f} which is equated to rigid  _m
-- So we must rigidify f.

okToRigidify ans [] = return ans
okToRigidify ans ((Equality r (term@(TyFun _ _ _))):ps) | (isRigid r == Rig) =
   do { (vs,_) <- get_tvs term; okToRigidify (union vs ans) ps}
okToRigidify ans ((Equality (term@(TyFun _ _ _)) r):ps) | (isRigid r == Rig) =
   do { (vs,_) <- get_tvs term; okToRigidify (union vs ans) ps}
okToRigidify ans (p:ps) = okToRigidify ans ps

fixate (loc,pat) preds =
  do { vs <- zonk preds >>= (okToRigidify [])
     ; let info = show pat
           fix (v@(Tv un flav k)) = do { tau <- newRigid loc info 0 Ex k; return(v,tau)}
     ; subs <- mapM fix vs
     ; preds' <- subT subs preds
     ; return (preds',subs) }


checkL caseOblig mod [] dom rng = return []
checkL caseOblig mod ((m@(loc,pat,body,ds)):ms) dom rng =
   do { (oblig',refinement) <- fixate (loc,pat) caseOblig
      ; (dom2,mod2) <- rigidity (subTau refinement dom)
      ; m2 <- typeMatch oblig' (modAnd mod mod2) m (Check(Rarrow (simpleSigma dom2) rng))
      ; ms2 <- checkL caseOblig mod ms dom rng
      ; return(m2:ms2) }

--------------------------------------------------------------------
-- Stmts are Typable

tcStmts mod m b [] = failD 2 [Ds "Do should have at least one statement"]
tcStmts mod m b [NoBindSt loc e] =
   case e of  -- (do { a; return b}::M z) is very common, but propogating the
              -- expected type ((return b)::M z) is hard, because (return b)
              -- is a function application. If the function is "return", there
              -- is a very simple and efficient rule. check (b::z)
     App (rexp@(Var (Global "return"))) x -> 
      do { (K _ retSig,rmod,rn,rexp) <- lookupVar (Global "return")
         ; retT <- returntype m
         ; morepoly "return" retSig retT
         ; e2 <- newLoc loc (typeExp mod x (Check (Rtau b)))
         ; return([NoBindSt loc (App rexp e2)])}
     other -> 
      do {e2 <- newLoc loc (typeExp mod e (Check (Rtau (TyApp m b))))
         ; return([NoBindSt loc e2])}
tcStmts mod m b [st@(BindSt loc pat e)] =
   failD 2 [Ds ("Last stmt in Do must not be a bind: "++show st)]
tcStmts mod m b [st@(LetSt loc ds)] =
   failD 2 [Ds("Last stmt in Do must not be Let: "++show st)]
tcStmts mod m b ((LetSt loc ds):ss) =
   do { (frag,ds2) <- inferBndrForDecs "let" localRename ds
      ; ss2 <- underFrag ("do { let ds; ... }",starR) (markLet frag) (tcStmts mod m b ss)
      ; return((LetSt loc ds2):ss2)}
tcStmts mod m b ((NoBindSt loc e):ss) =
   do { a <- newTau star
      ; e2 <- typeExp Wob e (Check (Rtau(TyApp m a)))
      ; ss2 <- tcStmts mod m b ss
      ; return((NoBindSt loc e2):ss2)}
tcStmts mod m b ((BindSt loc pat e):ss) =
   do { a <- newTau star
      ; (e2,oblig) <- peek (typeExp Wob e (Check(Rtau(TyApp m a))))
      -- Smart scrutinee from "Simple Unification-based Type Inference for GADTs"
      ; (oblig',refinement) <- fixate (loc,pat) oblig
      ; (a2,mod2) <- rigidity (subTau refinement a)
      ; (frag,p2) <- newLoc loc $ checkBndr localRename mod (addPred oblig' nullFrag) (simpleSigma a2) pat
      ; let frag1 = (markLambda frag)
      ; let comp theta = do { b2 <- appTheta mod theta b
                            ; tcStmts (modAnd mod mod2) m b2 ss }
      ; ss2 <- underFragUsingTheta ("do { "++show pat++" <- e; ... }",starR) frag1 comp
      ; return((BindSt loc p2 e2):ss2)}

----------------------------------------------------------------------

rigidity t =
  do { t2 <- zonk t; return(t2,isRigid t2)}

modAnd Rig x = x
modAnd Wob _ = Wob

isRigidR (Rtau x) = isRigid x
isRigidR x = Wob

isRigid (TcTv(Tv _ (Rigid _ _ _) _)) = Rig
isRigid (TcTv(Tv _ _ _)) = Wob
isRigid (TyApp x y) = modAnd (isRigid x) (isRigid y)
isRigid (TyCon sx _ _ _) = Rig
isRigid (Star n) = Rig
isRigid (Karr x y) = modAnd (isRigid x) (isRigid y)
isRigid (TyVar _ _) = Rig
isRigid (TySyn _ _ _ _ x) = isRigid x
isRigid (TyEx zs) = case unsafeUnwind zs of
                     (vs,(ps,tau)) -> isRigid tau
isRigid (TyFun f k xs) = if (all rigid (map isRigid xs)) then Rig else Wob
  where rigid Rig = True
        rigid _ = False


unifyMonad :: TyCh a => Expected Rho -> a (Tau,Tau)
unifyMonad (Check (Rtau (TySyn nm n fs as t))) = unifyMonad (Check (Rtau t))
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

inferBs :: Bool -> Frag -> [Pat] -> TC([Sigma],Frag,[Pat])
inferBs rename k [] = return([],k,[])
inferBs rename k (p:ps) =
  do { (sig,k2,p2) <- inferPat rename k p
     ; (sigs,k3,ps2) <- inferBs rename k2 ps
     ; return(sig:sigs,k3,p2:ps2)}

inferBndrs rename frag ps =
  do { (sigmas,frag,ps) <- inferBs rename frag ps
     ; return(sigmas,frag,ps)}

-- checkBndrs rename mod frag [p1,p2,p3] (t1 -> t2 -> t3 -> result)
-- checkThat:  theta <- check[p1:t1, p2:t2, p3:t3], and return theta(result)

checkBs :: Bool -> Mod -> Frag -> [Pat] -> Rho -> TC(Frag,[Pat],[Sigma],Rho)
checkBs rename mod f0 [] result =
  do { ty <- applyTheta Wob f0 result; return(f0,[],[],ty) }
checkBs rename mod f0 (p:ps) rho =
  do { (dom,rng) <- unifyFun rho
     ; (f1,p1) <- checkPat rename mod f0 dom p
     ; rng2 <- applyTheta Wob f1 rng
     ; (f2,ps2,ts,rng3) <- checkBs rename mod f1 ps rng2
     ; return(f2,p1:ps2,dom:ts,rng3)
     }

checkBndrs rename mod f0 ps result =
  do {(frag,ps,ts,rng) <- checkBs rename mod f0 ps result
     ; return(frag,ps,ts,rng)}

-------------------------------------------------------
-- Var is a TypableBinder

instance TypableBinder Var where
  checkBndr rename mod k t var =
     do { level <- getLevel
        ; v <- alphaN rename var
        ; ans <- addTermVar (var,(K [] t,Rig,level,Var v),LamBnd) k
        ; return(ans,v) }
  inferBndr rename k var =
     do { sigma <- newSigma star;
        ; level <- getLevel
        ; v <- alphaN rename var
        ; ans <- addTermVar (var,(K [] sigma,Wob,level,Var v),LamBnd) k
        ; return(sigma,ans,v) }

alphaN :: Fresh m => Bool -> Var -> m Var
alphaN True (Global s)  = do { nm <- fresh; return(Alpha s nm)}
alphaN True (Alpha s _) = do { nm <- fresh; return(Alpha s nm)}
alphaN False name = return name

---------------------------------------------------------------
-- A Pat is a TypeableBinder

instance TypableBinder Pat where
  checkBndr renm mod frag expect pat =
      do { (f,p) <- checkPat renm mod frag expect pat
         ; return(f,p)}
  inferBndr = inferPat

inferPat :: Bool -> Frag -> Pat -> TC(Sigma,Frag,Pat)
inferPat rename k pat =
  do { sigma <- newSigma star
     ; (k2,p2) <- checkPat rename Wob k sigma pat
     ; sigma2 <- zonk sigma
     ; return (sigma2,k2,p2)}

exFree d x = displays d [Dd x, Ds " = ",Ds(shtt x)]

removeSyn (Forall (Nil([],Rtau(TySyn _ _ _ _ x)))) = (Forall (Nil([],Rtau x)))
removeSyn x = x

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
          ; ans <- addTermVar (var,(K [] t,mod,level,Var v),LamBnd) k
          ; return(ans,Pvar v)}
    (Pcon c ps,Wob) ->
       do { (polyk,mod,n,exp) <- lookupVar c
          ; (vs,assump,rho) <- existsInstance (arisesPat pat) (show pat) polyk
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
          ; let k3 = addEqs (assump++emittedAssump) k2
          ; let k4 = addPVS (vs \\ bc) k3
          ; return(k4,Pcon c ps2)   }
    (Pcon c ps,Rig) ->
       do { (polyk,mod,n,exp) <- lookupVar c
          ; expect <- applyTheta Rig k t
          ; name <- showMdisp [Dd pat] 
          ; (vsC,assump,rhoC) <- rigidInstance (arisesPat pat) name polyk
          ; (vsExpect,oblig,rhoExpect) <- rigidInstance (arises2 expect) name (K [] expect)
          
          -- rhoC::    t1 -> t2 -> Ts s1 s2
          -- rhoExpect::           Tu u1 u2
          -- check that Tu==Ts, mguStar "(C p1 .. pn)" [(u1,s1),(u2,s2)]
          ; (pairs,tauC) <- constrRange c ps rhoC []
          ; tauExpect <- okRange c rhoExpect
          ; (us,_) <- get_tvs tauExpect
          -- down (Tu u1 u2) (Ts s1 s2) ==> [(u1,s1),(u2,s2)] when Tu==Ts
          ; let down (TySyn nm n vs args x) y = down x y
                down y (TySyn nm n vs args x) = down y x
                down (u@(TyCon sx _ tu _)) (s@(TyCon tx _ ts _)) | tu==ts = return []
                down (var@(TcTv (Tv un (Rigid _ _ _) k))) typ = return [(var,typ)]
                down (u@(TyCon sx _ tu _)) (s@(TyCon tx _ ts _)) =
                  failD 2 [Ds "\nWhile checking pattern: ",Dd pat
                          ,Ds "\n   the expected type: ",Dd u,Ds "\n   doesn't match the inferred type: ",Dd s]
                down (TyApp tu u) (TyApp ts s) =
                  do { ps <- down tu ts; return((u,s):ps) }
                down x y = failD 2 [Ds "\nWhile checking rigid pattern: ",Dd pat
                                   ,Ds "\nexpected type: ",Dd expect
                                   ,Ds "\ndoesn't match actual type: ",Dd rhoC
                                   ,Ds "\nunder refinement: ",Dl (getTheta k) ", "
                                   ,Ds "\n ",Dd x,Ds " =/= ",Dd y]
                addRigid (pat,sigma) = (pat,sigma,Rig)
          ; thingsToUnify <- down tauExpect tauC
          ; loc <- getLoc
          ; rhoCref <- newRef rhoC  -- we need to describe the pat type, but we haven't computed it yet.
          ; eitherInfo <- mguStar (describePat pat rhoCref,loc) vsC thingsToUnify
          ; case eitherInfo of
             Right(s,x,y) -> badRefine pat tauExpect tauC s x y
             Left(psi,truths) ->
               do { writeRef rhoCref (subRho psi rhoC)  -- BackPatch Pattern description
                  ; let triples = (map (addRigid) pairs)
                  ; k2 <- addUnifier psi (addPVS vsC k)
                  ; let k3 = addEqs (truths ++ subPred psi assump) k2
                  ; (k4,ps2) <- checkPats rename k3 triples
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
          ; let k2 = addEqs truths k1
          ; return(k2,Psum inj p1)}
    (z@(Pexists p),_) ->
      do { expect <- applyTheta Rig k t;
       case expect of
        Forall (Nil([],Rtau(TyEx zs))) ->
          do { loc <- getLoc
             ; (rigid,assump,tau) <- rigidInstanceL (arisesPat p . Rtau) (show pat) [] zs
             ; (k2,p2) <- checkPat rename Rig k (Forall(Nil([],Rtau tau))) p
             ; let k3 = addEqs assump k2
             ; let k4 = addPVS rigid k3
             ; return(k4,Pexists p2) }
        _ -> failD 1 (nonRigidExists t z)}
    (Paspat var p,_) ->
       do { (k1,p1) <- checkPat rename mod k t p
          ; level <- getLevel
          ; v <- alphaN rename var
          ; k2 <- addTermVar (var,(K [] t,Rig,level,Var v),LamBnd) k1
          ; return(k2,Paspat v p1)}
    (Pwild,_) -> return(k,Pwild)
    (Pann p ty,_) ->
       do { scopedEnv <- extendToEnv k
          ; loc <- getLoc
          ; (sigma,_) <- inEnv scopedEnv (checkPT (show pat) loc ty)
          ; eitherInfo <- morepolySS [] t sigma
          ; case eitherInfo of
             Right(s,x,y) -> failD 2 [Ds "Annotation not polymorphic enough.\n"
                                     ,Ds s,Dd x,Dd y]
             Left(psi,truths) ->
               do { (k2,p') <- checkPat rename Rig k sigma p
                  ; k3 <- addUnifier psi k2
                  ; let k4 = addEqs truths k3
                  ; return(k4,Pann p' ty)}}
    (ExtP x,_) ->
       do { exts <- getSyntax
          ; loc <- getLoc
          ; let lift0 nm = Pcon (Global nm) []
                lift1 nm x = Pcon (Global nm) [x]
                lift2 nm x y = Pcon (Global nm) [x,y]
                lift3 nm x y z = Pcon (Global nm) [x,y,z]
          ; new <- buildExt (show loc) (lift0,lift1,lift2,lift3) x exts
          ; checkPat rename mod k t new
          }


ifEqualPredThenAddAssump t frag =
  do { tau <- zonk t
     ; case tau of
        (TyApp (TyApp (TyCon sx lev "Equal" k) x) y) ->
                 (return(addEqs [(Equality x y)] frag))
        other -> return frag
     }

tauToPred (TyApp (TyApp (TyCon sx lev "Equal" k) x) y) = Equality x y
tauToPred tau = Rel tau

-- functions to make reasonable error reporting

badRefine pat expect computed s x y =
  do { kindelems <- showKinds2 (expect,computed)
     ; failK "bad refinement" 2
          [Ds "\nWhile inferring the type of the pattern: ",Dd pat
          ,Ds "\nwe expected it to have type: ",Dd expect
          ,Ds "\nbut we computed type: ",Dd computed
          ,Dr kindelems
          ,Ds "\nbut, the current refinement fails because ",Dd x,Ds " != ",Dd y
          ,Ds ".\nSometimes reordering the patterns can fix this."]}

badRefine2 pat theta t s =
  failK "bad refinement" 2
   [Ds "The current refinement: ",Dd theta,Ds "\nwon't type the pattern: "
   ,Dd pat,Ds " with type: ",Dd t
   ,Ds ".\nSometimes, when the type of one pattern depends on another,\nreordering the patterns might fix this.",Ds ("\n"++s)]


nonRigidExists t z =
  [Ds "Exists patterns cannot have their type inferred:\n  "
  ,Dd z,Ds "\nUse a prototype signature with 'exists t . type[t]' to enable type checking."
  ,Ds "\nThe current expected type is: ",Dd t,Ds ", which is not an existential."]

-- helper functions

constrRange c [] rho pairs =
  do { tau <- okRange c rho; return(reverse pairs,tau)}
constrRange c (p:ps) t pairs =
   do { (dom,rng) <- unifyFun t
      ; constrRange c ps rng ((p,dom):pairs)}

-- A range is Ok if its 1) a Tau type, 2) A TyCon type, 3) At Level 1
okRange c (Rtau t) = help t
  where help (TySyn _ _ _ _ x) = help x
        help (TyCon synext level nm polykind) =
           do { unifyLevel "okRange" level (LvSucc LvZero)
              ; return t }
        help (TyApp f x) = help f
        help (tf@(TyFun nm k args)) =
          do { (new,(levelvars,un),ps) <- nfTau tf
             ; case (un,ps) of
                ([],[]) -> do { warnM [Ds "\nTYFUN\n ",Dd new ]; help new}
                _ -> fail "TyFun in okRange" }
        help t = failD 2 [Ds "\nNon type constructor: ",Dd t,Ds " as range of constructor: ",Dd c]
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

getDecTyp :: Bool -> [Dec] -> TC (Frag,[(Mod,Rho,Dec,[TcTv])])
getDecTyp rename [] = return(nullFrag,[])
getDecTyp rename (d:ds) =
  do { (frag1,mod,rho,d,skols) <- frag4OneDeclsNames rename d
     ; (frag2,triples) <- getDecTyp rename ds  -- do the rest of the list
     ; frag3 <- frag2 +++ frag1
     ; return(frag3,(mod,rho,d,skols):triples) }

-- Step 2. Check the bodies. All names bound in the mutually recursive
-- set of decls are already in the frag passed as input (See Step 1).

checkDec :: Frag -> (Mod,Rho,Dec,[TcTv]) -> TC Dec
checkDec frag (mod,_,Prim loc nm t,skols) = newLoc loc $ return(Prim loc nm t)
checkDec frag (mod,rho,Fun loc nm hint ms,skols) | unequalArities ms =
  failD 3 [Ds ("\n\nThe equations for function: "++show nm++", give different arities.")]
checkDec mutRecFrag (mod,rho,Fun loc nm hint ms,skols) = newLoc loc $
  do { let frag = (markLambda (addSkol skols mutRecFrag))
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
       ; (ms2,oblig) <- collectPred
                       (underFrag (show nm,rho) frag (mapM hasRho ms))
     ; solveDecObligations (show nm) rho (getEqs mutRecFrag) oblig
     ; return(Fun loc nm hint (map stripName ms2)) }
checkDec mutRecFrag (mod,rho,Val loc pat body ds,skols) = newLoc loc $
  do { let lhsString = bodyName pat body
     ; (declFrag,ds2) <- inferBndrForDecs lhsString localRename ds
     ; frag <- (declFrag +++ (addSkol skols mutRecFrag))
     ; (body2,oblig) <- collectPred (underFrag (lhsString,rho)(markLambda frag)
                                               (typeBody mod body (Check rho)))
     ; solveDecObligations lhsString rho (getEqs frag) oblig
     ; return(Val loc pat body2 ds2) }
checkDec mutRecFrag (mod,rho,Pat loc nm vs p,skols) = newLoc loc $
  do { ((Forall (Nil (assump,ty))),(Frag xs tvs tenv eqs theta rs exts),p2)
               <- lambdaExtend ("the pattern "++show p)
                               mutRecFrag (inferBndr False nullFrag p)

     ; argtys <- compareL vs (map projBindMode xs)
     ; let arr (K _ sig) rho = arrow sig rho
     ; morepoly (show nm) (foldr arr ty argtys) rho
     ; return(Pat loc nm vs p)}
checkDec frag (mod,rho,Reject s ds,skols) =
   handleM 7 (do { let message = bindingGroupNames "a where clause that binds" ds
                 ; ((frag2,ds2),cs) <- collectPred (inferBndrForDecs message localRename ds)
                 ; when (not(null cs)) (failD 6 [Ds "Unresolved constraints"])
                 ; tryToEval ds2
                 ; failD 8 [Ds ("\nReject test: '"++s++"' did not fail.")]}) errF
       -- Its is important the the inner fail have higher failure level (8) than
       -- the outer catching mechanism (7). Because if the decl doesn't fail we want to know.
 where errF n = do { outputString ("\n*** Negative test '"++ s ++ "' fails as expected.\n")
                   ; return (TypeSig Z (Global "##test") tunit')}
checkDec frag (mod,rho,t,skols) = failD 2 [Ds "Illegal dec in value binding group: ", Ds (show t)]


tryToEval decs = Tc(\ env ->
  do { env2 <- elaborate None decs (runtime_env env)
     ; return(env2,[])})

----------------------------------------------------------
-- helper functions

unequalArities ms = not(same(map arity ms))
  where arity (loc,ps,body,ds) = length ps
        same [] = True
        same [x] = True
        same (x:y:zs) | x==y = same (y:zs)
        same _ = False

badOblig oblig oblig2 pat assump truths =
  do { r <- maybeM (refutable oblig2) return (return (Ds ""))
     ; failD 3 [Ds "\nWhile type checking: ", Dd pat
               ,Ds "\nUnder the truths: "
               ,Dl (assump++truths) ", "
               ,Ds "\nWe tried to solve: "
               ,Dl oblig ","
               ,Ds "\nBut we were left with: "
               ,Dl oblig2 ", ",r]}

solveDecObligations nm rho assump oblig =
 do { env <- tcEnv
    ; let truths = (assumptions env)
    ; (u,oblig2,_,_) <- solveConstraints (nm,rho) (env{assumptions = assump++truths}) oblig
    ; when (not (null oblig2)) (badOblig oblig oblig2 nm assump truths)}


refute [] term = return True
refute ((r@(RW nm key (Rewrite b) _ _ _ _)):rs) term = refute rs term
refute ((r@(RW nm key BackChain _ _ _ _)):rs) term = refute rs term
refute ((r@(RW nm key Refinement _ _ _ _)):rs) term = refute rs term
refute ((r@(RW nm key Axiom   _ _ _ _)):rs) term =
  do { (Rel lhs) <- freshLhs r
     ; test <- mguStar (return "from function refute",Z) [] [(lhs,term)]
     ; case  test of
        Left (sub,eqns) -> return False
        Right _ -> refute rs term
     }

refutable :: [Pred] -> TC (Maybe(DispElem Z))
refutable [] = return Nothing
refutable ((Rel term):ps) =
  do { t <- zonk term
     ; s <- predNameFromTau term t
     ; rules <- getMatchingRules isBackChain s
     ; ifM (refute rules t)
           (return(Just(Dr [Ds "\nThe proposition: (",Dd t,Ds ") is refutable."])))
           (refutable ps) }
refutable (p:ps) = refutable ps

predNameFromTau s (TyApp f y) = predNameFromTau s f
predNameFromTau s (TyCon sx l nm k) = return nm
predNameFromTau s x = failD 2 [Ds "\nNon Type constructor: "
                       ,Dd x
                       ,Ds " used as Prop in:\n  "
                       ,Dd s]

newf name Ex k =
  do { loc <- getLoc
     ; newRigid loc "skolem var in rewrite rule" name Ex k
     }
newf name q k = newflexi name q k

freshRule :: (Name -> Quant -> Kind -> TC Tau) -> RWrule ->  TC (Bool,[(TcTv,Quant)],[Pred],Pred,[Pred])
freshRule new (RW nm key rclass args precond lhs rhs) =
    do { (env,pairs) <- buildEnv newf args [] []
       ; precond2 <- subst env precond
       ; lhs2 <- subst env lhs
       ; rhs2 <- subst env rhs
       ; let commutes (Rewrite b) = b
             commutes _ = False
       ; return(commutes rclass,pairs,precond2,lhs2,rhs2)}

freshLhs :: RWrule -> TC Pred
freshLhs (RW nm key rclass args precond lhs rhs) =
    do { (env,pairs) <- buildEnv newflexi args [] []
       ; subst env lhs
       }

instanceOf args lhs rhs =
 do { (env,pairs) <- buildEnv newflexi args [] []
    ; lhs' <- subst env lhs
    ; rhs' <- subst env rhs
    ; eitherM (mguB [(lhs',rhs')])
        (\ unifier -> return True)
        (\ _ -> return False) }

buildEnv newf [] env pairs = return (env,pairs)
buildEnv newf ((nm,k,q):xs) env pairs =
         do { k2 <- subst env k
            ; (var@(TcTv v)) <- newf nm q k2
            ; buildEnv newf xs ((nm,var):env) ((v,q):pairs) }

-- ====================================================================
-- Types in syntax are stored as PT, we need to translate them
-- into Sigma types, and check that they are well formed with Kind *
-- PT types stored in Data Decs are handled differently because they
-- may have kinds other than *, and they are not always generalized.
-- We return a Sigma type, and a Fresh Rho type, and update the Display so it maps
-- the Vars in the fresh Rho to the Strings in the PT

compX new old = do { xs <- mapM f old; return(xs++new)}
  where f (nm,tau) = do { tau2 <- sub (new,[],[],[]) tau; return(nm,tau2)}


errX pt s = failD 2 [Ds "The prototype:  ",Dd pt,Ds "\ndoes not have kind *0, because ",Ds s]



        
checkPT :: String -> Loc -> PT -> TC(Sigma,(Rho,[Pred],[TcTv]))
checkPT name loc pt =
  do { tenv <- getTypeEnv
     ; (levels,sigma) <-
           case pt of
             (PolyLevel vs t) -> do { us <- freshLevels vs; return(us,t) }
             other -> return ([],other)
     ; (snMap,names,eqns,rho) <- inferConSigma levels tenv loc ([],sigma)
     ; let s = Forall (windup names (eqns,rho))
     ; handleM 2 (check s (Star LvZero)) (errX pt) -- check the translation has kind *0
     ; (nameMap,skol) <- rigid snMap names []      -- build the mappings
     ; rho2 <- sub (nameMap,[],[],[]) rho          -- make fresh Rho
     ; mapM (arises6 name rho2) skol
     ; eqn2 <- sub (nameMap,[],[],[]) eqns         -- and fresh equations
    -- ; warnM [Ds "\ncheckPT names = ",Dl names ", ",Ds "\n snMap = ",Dl snMap ", "
    --         ,Ds "\n nameMap = ",Dl nameMap ", "]
     ; return (s,(rho2,eqn2,skol))}
  where rigid ((s,nm):xs) ((nm2,k,q):ys) subst =
            do { k2 <- sub (subst,[],[],[]) k   -- in explicit foralls, earlier may bind
               ; let syn = if nm==nm2 then s else (show nm2)
               ; v <- newRigidTyVar q loc (return syn) k2  -- later, so we need to apply subst to k
               ; subst2 <- compX [(nm2,TcTv v)] subst
                 -- the infered names (ys) my include types not in the explicit (xs) , skip over such
               ; (subst3,skols) <- rigid (if nm==nm2 then xs else (s,nm):xs) ys subst2
               ; newname <- registerDisp syn v    -- Update the Display to map the rigid to the PT name
               ; return(subst3,v:skols)}
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
 where (free,freeLevels) = getFree (map name tenv) pt
       name (nm,tau,kind) = nm
       g nm = (nm,AnyTyp,All)

-- In a type synonym like:
-- type ListInt = [ Int ]
-- the type must be well kinded in the current environment

inferPT :: ToEnv -> PT -> TC(Tau,Kind,PolyKind)
inferPT argEnv pt =
  do { tenv <- getTypeEnv
     ; loc <- getLoc
     ; exts <- getSyntax
     ; s <- toTau (argEnv ++ tenv,loc,exts,[]) pt
     ; (k::Tau,ty) <- infer s

     ; return(ty,MK k,poly(MK k))
     }

inferPolyPT :: ToEnv -> PT -> TC(Sigma,Tau,PolyKind,[Name])
inferPolyPT argEnv pt =
  do { tenv <- getTypeEnv
     ; loc <- getLoc
     ; exts <- getSyntax
     ; let (levels,pt') = case pt of
                           (PolyLevel vs t) -> (vs,t)
                           other -> ([],pt)
     ; levs <- freshLevels levels
     ; (s,names) <- toSigma (argEnv ++ tenv,loc,exts,levs) pt'
     ; (k::Tau,ty) <- infer s
     ; let newName x = do { nm <- fresh; return(x,nm)}
     ; (vars,levelVars) <- get_tvs ty
     ; pairs <- mapM newName levelVars
     ; let env = ([],[],[],map (\ (x,y) -> (x,TcLv(LvVar y))) pairs)
     ; ty' <- sub env ty
     ; k' <- sub env k
     ; return(ty',k',poly(MK k'),map snd pairs {- names from free levels -})
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

introLorR (loc,Global "L",args,preds,typ) = True
introLorR (loc,Global "R",args,preds,typ) = True
introLorR (loc,var,args,preds,typ) = False


kindOfTyConFromDec (decl@(GADT loc isP (Global name) k cs ds _)) | any introLorR cs =
  failM 1 [Ds "\nThe data decl: ",Ds name,Ds " has a constructor named 'L' or 'R'."
          ,Ds "\nThese names are reserved for the sum type. L:: a -> (a+b), R:: b -> (a+b)"]
kindOfTyConFromDec (decl@(GADT loc isP (Global name) k cs ds _)) = newLoc loc $
  do { (vs,level,sigma) <- univLevelFromPTkind name k
     ; return(decl,(isP,name,sigma,level,loc,vs))}
kindOfTyConFromDec (decl@(Data loc isP _ (Global name) (Just k) vs cs derivs _)) =
  failM 1 [Ds "\nData decs should have been translated away.\n",Ds (show decl)]

-- Given T :: a ~> b ~> * ; data T x y = ... OR data T (x:a) (y:b) = ...
-- Bind the args to their kinds [(x,a),(y,b)]. If there is No kind
-- information, use default rules, which depend on the strata information
-- which must be either type or kind, since the explicit GADT form must
-- be used for other levels.

useSigToKindArgs:: Strata -> [(Var,PT)]-> Maybe PT -> TC([(String,PT,Quant)],PT)
useSigToKindArgs strata args sig = walk args sig where
  walk [] Nothing = return ([],Star' strata Nothing) -- implicit (T a b):: *
  walk [] (Just (Star' k n))= return ([],Star' k n)  -- explicit (T a b):: *
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

transDataToGadt ds = mapM getGADT ds
  where getGADT (d@(GADT _ _ _ _ _ _ _)) = return d
        getGADT (x@(Data _ _ _ nm _ _ cs derivs _)) =
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

----------------------------------------------------------------------------
-- Compute information for each type constructor, and each constructor function.
-- in a mutually recursive set of data decls. Proceeds in several steps.
-- 1) Compute kind schemas for all of the TyCons, and a univ level for each TyCon
-- 2) Then under these schemas, check that each ConstrFun's type is classified by (Star level)
-- E.g.  data T:: *0 ~> Nat ~> *0 where
--         C:: a -> Int -> T a Z
-- schema T::*0 ~> Nat ~> *0  with level *0, then check that (a -> Int -> T a Z) :: *0
-- Then add theorems and rules, and build a Frag to return.

-- When defining a level polymorphic type, these functions are used 
-- to specialize the types of constructors to live in the value name space
-- 1) Turn (x ~> y ~> T_(i)) into (x -> y -> T_(1))
-- 2) Make sure T has level one in the value name space, and all args [x,y] have level one as well

levelOf (TyCon syn level name kind) = [level]
levelOf (TyApp f x) = levelOf f
levelOf x = []

-- Return a list of all the levels that have to be fixed
-- basically in (a -> b -> T x) = [level a,level b,level T]
levelTau (TyCon syn level name kind) = [level]
levelTau (TyApp f x) = levelOf f
levelTau (Star n) = [LvSucc n]   -- is this right?
levelTau (Karr s t) = levelOf t
levelTau (TySyn _ _ _ _ x) = levelOf x
levelTau (TyEx x) = levelL levelTau x
levelTau x = []

levelRho (Rtau t) = levelTau t
levelRho (Rarrow s t) = levelRho t
levelRho (Rpair x y) = levelSigma x ++ levelSigma y
levelRho (Rsum x y) = levelSigma x ++ levelSigma y

levelSigma (Forall z) = levelL levelRho z
 
levelL f l = f r   where (polynames,(preds,r)) = unsafeUnwind l

-- Change all the (a ~> b ~> T) to (a -> b -> T) and also return 
-- a list levels needing fixing and the name and level of T
fixTau2 (Karr x y) = (tarr x y',levelOf x ++ list,nm) where (y',list,nm) = fixTau2 y
fixTau2 (TyApp f x) = (TyApp f' x,list,nm) where (f',list,nm) = fixTau2 f
fixTau2 x = (x,levelOf x,nameOf x)

fixRho2 (Rtau x) = (Rtau x',list,name) where (x',list,name) = fixTau2 x
fixRho2 (Rarrow s t) = (Rarrow s t',l2++l1,name) 
    where (t',l1,name) = fixRho2 t
          l2 = levelSigma s          
fixRho2 x = (x,[],("",LvZero))
       
fixSigma (Forall z) = (Forall (windup polynames (preds,t')),list,(name,lev))
  where (polynames,(preds,t)) = unsafeUnwind z
        (t',list,(name,lev)) = fixRho2 t
        
-- Actually specialize a level polymorphic sigma at level 0
specializeAt0 cname (K levelnames (Forall z)) = 
     do { let (sigma2,list2,(name,levl)) = fixSigma (Forall z)
	      levels2 = map (\ x -> (x,LvSucc LvZero)) list2
              good (TcLv (LvVar x)) name = x /= name
              good (LvSucc x) name = good x name
              good other name = True
        ; pairs <- case unifyLevels levels2 of
                     Nothing -> failM 1 [Ds "\nValue level of level polymorphic ",Dd name
                                        ,Ds " fails to be compatible with level 1 type\n"]                           
                     Just x -> return x
        ; sigma3 <- sub ([],[],[],pairs) sigma2
        ; (_,freelevels) <- get_tvs sigma3
        ; return (K (filter (good levl) levelnames) sigma3)
        }
        

unifyLevels :: [(Level,Level)] -> Maybe[(TcLv,Level)]
unifyLevels xs = walk [] xs
  where sub1 env (v,l) = (v,substLevel env l)
        sub2 env (l1,l2) = (substLevel env l1,substLevel env l2)
        walk env [] = Just env
        walk env ((LvZero,LvZero):more) = walk env more
        walk env ((LvSucc x,LvSucc y):more) = walk env ((x,y):more)
        walk env ((TcLv v,TcLv u):more) | u==v = walk env more
        walk env ((TcLv v,y):more) = walk env2 (map (sub2 env2) more)
          where env2 = ((v,y):(map (sub1 env) env))
        walk env ((y,TcLv v):more) = walk env2 (map (sub2 env2) more)
          where env2 = ((v,y):(map (sub1 env) env))          
        walk env ((x,y):more) = Nothing        
        
----------------------------------------------------------

checkDataDecs :: [Dec] -> TC (Sigma,Frag,[Dec])
checkDataDecs decls =
  do { ds <- transDataToGadt decls
     ; (ds2,env2,tyConMap) <- kindsEnvForDataBindingGroup ds   -- Step 1
     ; css <- mapM (constrType env2) ds2                       -- Step 2
     -- After checking ConFuns, zonk and generalize Type Constructors
     ; (tyConMap2) <- mapM genTyCon tyConMap
     -- Then generalize the Constructor functions as well
     ; conFunMap2 <- mapM (genConstrFunFrag tyConMap2) css >>= return . concat
     ; let ds2 =  map (\ (newd,synext,strata,isprop,zs) -> newd) css
           exts = filter (/= Ox) (map (\ (newd,synext,strata,isprop,zs) -> synext) css)

           lift [] types values = return (types,values)
           lift ((level,isProp,tag,(Global s,(polyk,mod,n,exp))):xs) types values =
             case (definesValues level,definesTypes level) of
               -- I.e. a Kind or above, the ConFuns are types not values!
              (False,True) -> lift xs ((s,TyCon tag level s (polyk),polyk):types) values
              (True,False) -> do { poly2 <- specializeAt0 s polyk
                                 ; lift xs types ((Global s,(poly2,mod,n,exp),LetBnd):values)}
              (True,True) -> do { poly2 <- specializeAt0 s polyk
                                ; lift xs ((s,TyCon tag level s (polyk),polyk):types)
                                          ((Global s,(poly2,mod,n,exp),LetBnd):values)}
     ; let proj (nm,tau,polykind,levs) = (nm,tau,polykind)
     ; (types,values) <- lift conFunMap2 (map proj tyConMap2) []
     ; let makeRule (level,False,_,(Global c,(polyk,mod,_,_))) = return []
           makeRule (level,True,_,(Global c,(K lvs sigma,mod,_,_))) = sigmaToRule (Just Axiom) (c,sigma)
     ; rules <- mapM makeRule conFunMap2
     ; return(simpleSigma unitT,Frag values [] types [] [] (concat rules) exts,ds2)
     }

-- given:  data T:: *n where ...
-- T defines values if *n = *0 or is level polymorphic

definesValues LvZero = True
definesValues (TcLv _) = True
definesValues (LvSucc _) = False

definesTypes LvZero = False
definesTypes (TcLv _) = True
definesTypes (LvSucc _) = True

genConstrFunFrag tyConInfo (d2,tag,strata,isProp,conFunInfo) = mapM f conFunInfo
  where f (nm::Var,(sig::Sigma,mod::Mod,lev::CodeLevel,exp::Exp)) =
          do { -- Replace TyCon's which have stale PolyKind fields
               -- (i.e. they are monomorphic and non-level polymorphic)
             ; let fixKindLevel (nm,tau,polykind,levs) = 
                        do { k <- sub ([],[],[],levelsub) tau; return(nm,k)}
             ; tyConSub <- mapM fixKindLevel tyConInfo
             ; sig1 <- sub ([],[],tyConSub,levelsub) sig
             ; (_,w) <- generalize sig1  -- Now generalize
             ; return(strata,isProp,tag,(nm,(w,mod,lev,exp)))}
        levelsub = concat(map (\ (nm,tau,polykind,levs) -> levs) tyConInfo)


-- genTyCon :: (Bool,String,Tau,PolyKind) -> TC (String,Tau,PolyKind,[(TcLv,Level)])
genTyCon (isprop,nm,TyCon sx level _ _ ,K lvs k) =  -- Ignore the current lvs,
  do { (levs,K names k2) <- generalize k     -- we'll compute a more accurate one
     ; return(nm,TyCon sx level nm (K names k2),K names k2,levs) }


-- kindsEnvForDataBindingGroup:: [Dec] -> TC(ToEnv,[(Bool,String,Tau,PolyKind)])
kindsEnvForDataBindingGroup ds =
  do { env <- getTypeEnv
     ; loc <- getLoc
     ; info <- mapM kindOfTyConFromDec ds
     ; let parsekind levs name (kind@(Forallx _ _ _ _)) =
             do { exts <- getSyntax
                ; (sigma,_) <- toSigma (env,loc,exts,levs) kind
                ; return (levs,sigma)}
           parsekind levs name kind =
             do { (nmMap,vars,ps,rho) <- inferConSigma levs env loc ([],kind)
                ; return([],Forall(windup vars (ps,rho)))}
           addTyCon (d,(isP,name,kind,level,loc,freeLevVars)) (ds,delta,env) =
            do { (levs,sigma) <- parsekind freeLevVars name kind
               -- ; warnM [Ds "\nCheck kinding ",Dd sigma,Ds ":: ",Dd (Star (LvSucc level)),Dl freeLevVars ","]
               ; sigma' <- newLoc loc $
                           handleM 3 (check sigma (Star (LvSucc level)))
                                     (badKind name kind)
               ; s1 <- zonk sigma'
               ; let kind = K (map snd levs) sigma'
                     poly = TyCon Ox (LvSucc level) name kind
               ; return ((d,freeLevVars,level):ds
                        ,(name,poly,kind):delta
                        ,(isP,name,poly,kind):env)}
           delProp (isP,nm,tau,poly) = (nm,tau,poly)
     ; foldrM addTyCon ([],env,[]) info
     }

-------------------------------------
-- Parse a Constr's type with an implicit forall
-- C:: (P1,P2) => T x (y::x) -> T Int y
-- where there are no explicit kinds for the variables.
-- "bound" is names already in scope

inferConSigma levelMap currentMap loc ([],pt@(Forallx All _ _ _)) =
 do { exts <- getSyntax
    ; (sigma@(Forall l),nmMap) <- toSigma (currentMap,loc,exts,levelMap) pt
    ; let (vars,(ps,rho)) = unsafeUnwind l
    -- Some of the variables in the forall may leave their kinds implicit
    -- Some of these may be polymorphic, we need to add these to vars
    ; (k::Tau,sigma2) <- infer sigma      -- infers implicit kinds
    ; (free,levelvars) <- get_tvs sigma   -- collect them from sigma
    ; let f (v@(Tv uniq _ k)) = do { nm <- fresh; return((nm,k,All),(v,TyVar nm k))}
    ; pairs <- mapM f free                      -- abstract each variable with a new name
    ; let kindVars = map fst pairs              -- build the new var list
          env = ([],map snd pairs,[],[])        -- and build an env
    ; (vars',ps',rho') <- sub env (vars,ps,rho) -- sub them away with their new name
    ; return(nmMap,kindVars++vars',ps',rho')}
inferConSigma levelMap currentMap loc (preds@(p:ps),pt@(Forallx _ _ _ _)) =
 failM 2 [Ds "\nIllegal type in InferConMap: ",Dd (p:ps),Ds " => ",Dd pt]
inferConSigma levelMap currentMap loc (preds,typ) =
 do { let bound = map (\ (nm,tau,kind) -> nm) currentMap
          -- compute names (free or bound) in the type to be parsed
          (free,levels) = getFree [] typ `unionTwo` getFreePredL [] preds  -- [x,y,Int,T]
          args = map (\ nm -> (nm,AnyTyp,All)) (free \\ bound) -- [(x,any,All),(y,any,All)]
          zonkK (nm,k,q) = do { k2 <- zonk k; return(nm,k2,q) }
          fix rangeFree (nm,k,_) =
              if any (\(v,k) -> v==nm) rangeFree then (nm,k,All) else (nm,k,Ex)
    ; exts <- getSyntax
    ; (nmMap,windupList,envMap) <- argsToEnv args (currentMap,loc,exts,levelMap)
    ; rho <- toRho envMap typ
    ; ps <- toPred envMap (Just preds)
    ; rho2 <- zonk rho
    -- Zonk the kinds of the bound variables
    -- This may cause some kinds to appear in the range types
    -- because of types like, C:: T x (y::x) -> T Int y
    ; list2 <- mapM zonkK windupList
    ; (_,rangeFree,_) <- range varsOfTau rho2 rho2 -- Vars of the zonked range
    ; return(nmMap,map (fix rangeFree) list2,ps,rho2)}

range f b (Rarrow dom rng) = range f b rng
range f b (Rtau (Karr dom rng)) = range f b (Rtau rng)
range f b (Rtau (TyApp (TyApp (TyCon se lev "(->)" k) dom) rng)) = range f b (Rtau rng)
range f b (Rtau x) = return(f x)
range f b x = failM 1 [Ds "\nThe type: ",Dd b,Ds "\nis not a good type for a constructor function"]

-------------------------------
-- The type environment currentMap already includes information for all the type names
-- in the mutually recursive binding group of GADTs (See kindsEnvForDataBindingGroup).
-- We are just translating the constructors to Sigma types.

ds xs = Ds (concat xs)

constrType :: [(String,Tau,PolyKind)] -> (Dec,[(String,Name)],Level) ->
              TC (Dec,SynExt String,Level,Bool,[(Var,(Sigma,Mod,CodeLevel,Exp))])

constrType currentMap (GADT loc isProp tname tkind constrs derivs _,levels,strata) = newLoc loc $
    do { synTag <- checkDerivs constrs derivs
       ; let newd = (GADT loc isProp tname tkind constrs derivs synTag)
       ; zs <- mapM (processOneCon levels strata) constrs
       ; return(newd,synTag,strata,isProp,zs)}  where
 processOneCon levels strata (loc,cname, vars, preds, typ) =
    do { sigma <- parseSigma levels cname strata vars preds typ
       ; newLoc loc $
         handleM 3 (check sigma (Star strata))
                   (illFormed cname sigma (Star strata))
       ; sigma2 <- zonk sigma
       ; return(cname,(sigma2,Rig,0,Var cname))}
 parseSigma levels cname strata vars preds typ  =
    case vars of
     -- The constr leaves the kinding of vars implicit.  C:: T a -> T a
     [] -> do { checkRng cname tname strata typ
              ; (nmMap,vars,ps,rho2) <- inferConSigma levels currentMap loc (preds,typ)
              ; zvars <- zonk vars
              ; checkValuesDontUseKarr cname rho2 strata
              ; return(Forall(windup vars (ps,rho2)))}
     _  -> do { (_,rng) <- checkRng cname tname strata typ
              ; let bound = map (\ (nm,tau,kind) -> nm) currentMap
                    (typvars,_) = getFree [] rng
                    rngFree = typvars \\ bound
                    -- vars are Ex if they aren't in the range type
                    -- E.g. 'a' in   App:: Exp (a -> b) -> Exp a -> Exp b
                    -- except for *n: Eq:: forall (a:: *1) (b:: a) . Equal b b
                    quant (Star' _ _) n = All
                    quant _ n = if elem n rngFree then All else Ex
                    addQuant (name,kind) = (name,kind,quant kind name)
                    quantVars = map addQuant vars
                    sigmaPT = Forallx All quantVars preds typ
              ; exts <- getSyntax
              ; (sigma,nmMap) <- toSigma (currentMap,loc,exts,levels) sigmaPT
              ; return sigma}

checkValuesDontUseKarr cname (rho@(Rtau t)) LvZero | hasKarr t =
  failM 2 [Ds "\n\nThe constructor: ",Dd cname
          , Ds ", is supposed to be a value,\nbut it is classified by a kind arrow.\n"
          ,Dd cname,Ds":: ",Dd rho]
  where hasKarr (Karr x y) = True
        hasKarr x = case arrowParts x of
                     Just(dom,rng) -> hasKarr rng
                     Nothing -> False
checkValuesDontUseKarr cname x y = return()


-------------------------------------------------------
-- Check that the deriving clause is consistent with the constructors

checkDerivs constrs [] = return Ox
checkDerivs constrs xs =
  do { let (syns,_) = partition isSyntax xs
           unSyn (Syntax x) = x
     ; checkSyn constrs (map unSyn syns)
     }

checkSyn _ [] = return Ox
checkSyn _ (x:y:_) = failM 2 [Ds "\nA data declaration can have at most one syntax extension."]
checkSyn constrs [ext] =
  do { exts <- getSyntax
     ; failWhen ((elem ext exts)&& ((synName ext) /= "Nat") && ((show(synKey ext)) /= "")) 2
                [Ds "\nSyntax name for ",Ds (synName ext),Ds " already in use: ",Ds (show(synKey ext))]
     ; case (constrs,ext) of
        ([nilC,consC],Lx(key,_,_)) -> checkList key nilC consC
        (_,Nx(('o':_),_,_)) -> failM 2 [Ds "\nIllegal Nat-style syntax extension: 0o123 is reserved for octal integers."]
        (_,Nx(('x':_),_,_)) -> failM 2 [Ds "\nIllegal Nat-style syntax extension: 0xABC is reserved for hexadecimal integers."]
        ([zeroC,succC],Nx(key,_,_)) -> checkNat key zeroC succC
        ([pairC],Px(key,_)) -> checkPair key pairC
        ([rnilC,rconsC],Rx(key,_,_)) -> checkRecord key rnilC rconsC
        (cs,z) -> failM 2 [Ds "\nWrong number of constructors for syntax extension: ",Ds (synKey z)
                          ,Ds ". ",Ds name,Ds " extensions expect ",Dd size,Ds "."]
           where (name,size) = nameSize z
     }

nameSize :: SynExt a -> (String,Int)
nameSize (Lx _) = ("List",2)
nameSize (Nx _) = ("Nat",2)
nameSize (Px _) = ("Pair",1)
nameSize (Rx _) = ("Record",2)
nameSize Ox = ("",0)

count:: PT -> Int
count (Rarrow' x y) = 1 + count y
count (Karrow' x y) = 1 + count y
count x = 0

checkList key (_,Global nil,_,_,a) (_,Global cons,_,_,b)
    | count a==0 && count b==2 = return (Lx(key,nil,cons))
checkList key (_,Global nil,_,_,a) (_,Global cons,_,_,b) =
  tell "List" ("Nil",nil,a) 0 ("Cons",cons,b) 2


checkRecord key (_,Global rnil,_,_,a) (_,Global rcons,_,_,b)
   | count a==0 && count b==3 = return (Rx(key,rnil,rcons))
checkRecord key (_,Global rnil,_,_,a) (_,Global rcons,_,_,b) =
  tell "Record" ("Rnil",rnil,a) 0 ("Rcons",rcons,b) 3

checkNat key (_,Global zero,_,_,a) (_,Global succ,_,_,b)
   | count a==0 && count b==1 = return (Nx(key,zero,succ))
checkNat key (_,Global zero,_,_,a) (_,Global succ,_,_,b) = tell "Nat" ("Zero",zero,a) 0 ("Succ",succ,b) 1

checkPair key (_,Global pair,_,_,a) | count a==2 = return (Px(key,pair))
checkPair key (_,Global pair,_,_,a) =
   failM 2 [Ds"\nFor a Pair extension\n the (,) constructor (",Ds pair,Ds ":: ",Dd a
           ,Ds ") should have 2 arguments, not ",Dd (count a)]

tell:: String -> (String,String,PT) -> Int -> (String,String,PT) -> Int -> TC a
tell key (x1,nm1,a) n1 (x2,nm2,b) n2 =
  failM 2 [Ds"\nFor a ",Ds key,Ds " extension\n the ",Ds x1,Ds " constructor (",Ds nm1,Ds ":: ",Dd a,Ds ") should have "
          ,Dd n1,Ds " arguments and\n the ",Ds x2,Ds " constructor (",Ds nm2,Ds ":: ",Dd b,Ds ") should have ",Dd n2
          ,Ds " arguments."]

isSyntax (Syntax _) = True
isSyntax _ = False

failWhen test n xs = if test then failM n xs else return ()

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
checkRng c tname LvZero (Rarrow' d x) =
  do { (ds,r) <- checkRng c tname LvZero x; return(d:ds,r) }
checkRng c tname (LvSucc lev) (Karrow' d x) =
  do { (ds,r) <- checkRng c tname (LvSucc lev) x; return (d:ds,r)}
checkRng c tname (TcLv lev) (Karrow' d x) =
  do { (ds,r) <- checkRng c tname (TcLv lev) x; return (d:ds,r)}  
checkRng c (Global tname) _ (t@(TyCon' nm _)) | tname == nm = return ([],t)
checkRng c (Global tname) _ (t@(TyVar' nm)) | tname == nm = return ([],t)
checkRng c (Global tname) _ (t@(TyApp' _ _)) = down t
  where down (TyApp' (TyCon' s _ ) x) | s==tname = return ([],t)
        down (TyApp' (TyVar' s) x) | s==tname = return ([],t)
        down (TyApp' x y) = down x
        down t = failD 2 [Ds "\nThe range of the constructor: ",Dd c
                         ,Ds " is not an application of: "
                         ,Dd tname,Ds ".\nInstead it is: ",Dd t,Ds("\ninternal representation: "++shtt t)]
checkRng c tname lev typ =
  failD 2 [Ds "\nThe range of the constructor: ",Dd c,Ds " is not "
          ,Dd tname,Ds ".\nInstead it is: ",Dd typ, Ds " (at level ",Dd lev,Ds ")",perhaps]
     where perhaps = case typ of 
                      (Rarrow' dom rng) ->  Dr [Ds "\nPerhaps you meant: ",Dd (Karrow' dom rng)]
                      other -> Ds ""
                            
                            
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

data2gadt (Data loc isP strat tname@(Global nm) hint args cs derivs exts) =
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
    ; return(GADT loc isP tname kind (map each cs) derivs exts)
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

bindingGroupNames letOrWhere ds = message
  where names = concat(map dnames ds)
        (_,message) = displays disp0 [Ds (" "++letOrWhere++" "),Dl names ","]



inferBndrForDecs :: String -> Bool -> [Dec] -> TC (Frag,[Dec])
inferBndrForDecs letOrWhere renam [] = return(nullFrag,[])
inferBndrForDecs letOrWhere renam ds =  many dss
  where (dss,pairs) = topSortR freeOfDec ds
        many [] =  return(nullFrag,[])
        many ([]:dss) = many dss
        many (ds:dss) =                                      -- For each mutually recursive nest
           do { (_,frag1,xs) <- inferBndr renam nullFrag ds  -- MOST OF THE WORK DONE HERE
              ; let message = bindingGroupNames letOrWhere ds
                              -- previous nests, can be seen by later nests, so use "underLet"
              ; (frag2,ys) <- underFrag (message,starR) (markLet frag1) (many dss)
              ; frag3 <- frag2 +++ frag1
              ; return (frag3,xs++ys)}

-- Used in Step 1 (of inferBndr), to get a frag for the names bound in a single decl
-- In a mutually recursive nest, these Frags are all (+++) together.

frag4OneDeclsNames rename (d@(Val loc (Pann pat pt) body ds)) = newLoc loc $
  do { (sigma,(rho,assump,skol)) <- checkPT (show pat) loc pt    -- use the hint to get rho and display
     ; (frag,pat2) <- checkBndr rename Rig nullFrag sigma pat
     ; return(addPred assump (addSkol skol frag),Rig,rho,Val loc pat2 body ds,skol)}
frag4OneDeclsNames rename (Val loc pat body ds) = newLoc loc $
  do { info <- guess (loc,pat) body
     ; case info of
        (Just t,Rig) ->
           do { -- warnM [Ds "Guessing ",Dd body,Ds ":: ",Dd t]
              ; (frag,pat2) <- checkBndr rename Rig nullFrag (simpleSigma t) pat
              ; return(frag,Rig,Rtau t,Val loc pat2 body ds,[])}
        (any,mod) ->
           do { (sigma,frag,pat2) <- inferBndr rename nullFrag pat
              ; (rigid,assump,rho) <- rigidTy Ex loc (show pat) sigma
              ; return(addPred assump frag,mod,rho,Val loc pat2 body ds,[])}
     }
frag4OneDeclsNames rename (Fun loc nm Nothing ms) = newLoc loc $
  do { sigma <- newSigma star
     ; (frag,nm2) <- checkBndr rename Wob nullFrag sigma nm
     ; (rigid,assump,rho) <- rigidTy Ex loc (show nm) sigma
     ; r1 <- zonk rho
     ; return(addPred assump frag,Wob,r1,Fun loc nm2 Nothing ms,[])}
frag4OneDeclsNames rename (Fun loc (nm@(Global fname)) (Just pt) ms) = newLoc loc $
  do { (sigma,(rho,assump,skol)) <- checkPT fname loc pt -- use the hint to get rho and display
     ; s1 <- zonk sigma
     ; (frag,nm2) <- (checkBndr rename Rig nullFrag sigma nm)
     ; r1 <- zonk rho
     ; return(addPred assump (addSkol skol frag),Rig,r1,Fun loc nm2 (Just pt) ms,skol)}
frag4OneDeclsNames rename (Pat loc nm vs p) = newLoc loc $
  do { (sigma,frag,nm2) <- inferBndr rename nullFrag nm
     ; (rigid,assump,rho) <- rigidTy Ex loc (show nm) sigma
     ; return(addPred assump frag,Wob,rho,Pat loc nm2 vs p,[])}
frag4OneDeclsNames rename (Reject s ds) = return (nullFrag,Wob,Rtau unitT,Reject s ds,[])
frag4OneDeclsNames rename (Prim l nm t) =
  do { (sigma,frag,_) <- inferBndr rename nullFrag (Pann (Pvar nm) t)
     ; return(frag,Wob,error "Shouldn't Check Prim type",Prim l nm t,[]) }
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
  do { (K lvs sigma,Rig,n,exp) <- lookupVar c
     ; (preds,Rtau tau) <- instanTy lvs sigma
     ; return tau}
scrType t@(App f x) =
  do { ftyp <- scrType f
     ; xtyp <- scrType x
     ; rng <- newTau star
     ; unify (tarr xtyp rng) ftyp
     ; return rng }
scrType x  = fail "does not have scrShape"

scrMod pair term | not(scrShape term) = return (Nothing,Wob)
scrMod pair term =
  handleM 99 (do { t <- scrType term
                 ; (t2,mod) <- rigidity t
                 ; return (Just t2,mod)})
             (\ n -> return (Nothing,Wob))

guess pair (Normal exp) = scrMod pair exp
guess pair _ = return (Nothing,Wob)

------------------------------------------------------------------------
-- Helper functions for typing [Dec]

-- rigidTy is called when checking the body of a Dec with an explicit
-- type signature. It replaces all type variables with kinds classified
-- by *1 (i.e. *0 or other kinds classified by *1) with
-- new rigid type variables. For example a type like
-- (forall (k:*1) (u:k) a . (AtomX u) -> a -> Pair)
-- should rigidify "u" and "a", but not "k"

rigidTy :: TyCh m => Quant -> Loc -> String -> Sigma -> m([TcTv],[Pred],Rho)
rigidTy q loc s sigma = unBindWith (arises4 s) (newRigid loc s) sigma
 

bodyName pat (Normal e) = show pat
bodyName pat (Guarded _) = "the guarded pattern: "++show pat
bodyName pat Unreachable = show pat ++" = unreachable"

-- Generalize a Frag after type inference
genFrag (Frag xs ys tenv eqs theta rs exts) =
     do { zs <- mapM gen xs; return(Frag zs ys tenv eqs theta rs exts)}
  where gen (var,(K [] (sigma@(Forall (Nil b))),mod,level,exp),mode) =
            do { s1 <- zonk sigma
               ; (_,s2) <- generalize b; return (var,(s2,mod,level,exp),LetBnd)}
        gen (var,(sigma,mod,level,exp),mode) =
            do { s2 <- zonk sigma; return(var,(s2,mod,level,exp),LetBnd) }

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

fff d (x,y,z) = displays d [Ds x,Ds " :: ",Dd y,Ds "(",Dl z ",",Ds ")"]

escapes :: TyCh m =>  [(String,Sigma,[TcTv])] -> [TcTv] -> m ()
escapes trips [] = return ()
escapes trips bad = do { as <- getBindings
                       ; d0 <- readRef dispRef
                       ; (display,lines) <- foldrM (f as) (d0,"") bad
                       ; writeRef dispRef display
                       ; failK "escapes" 2 [Ds lines] }
  where f as (v@(Tv _ (Rigid All loc (s,ref)) k)) (d1,str) =   
           (do { (d2,typing) <- get d1 v trips
               ; comp <- readRef ref
               ; www <- fromIO comp
               ; let elements = [Dlf fff trips ";",Ds "\nThe prototype gives a type where the variable: "
                                ,Dd v,Ds ("\narising from the pattern "++www)
                                ,Ds " is polymorphic.\nBut, this is not the case. "
                                ,Ds "The context demands the typing ",Ds (typing++".")]
               ; return(displays d2 elements)})
        f as (v@(Tv _ (Rigid Ex loc (s,ref)) k)) (d1,str) =   
          do { (d2,var) <- get d1 v trips
             ; comp <- readRef ref
             ; www <- fromIO comp
             ; return $
                displays d2
                  [Ds "\nAn existential type var: ", Dd v
                  ,Ds ("\narising from the pattern: "++www)
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
escapeCheck term typ (Frag _ skolvars _ _ _ _ _) =
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

lookupVar :: Var -> TC (PolyKind,Mod,CodeLevel,Exp)    -- May fail
lookupVar n = do { env <- getTCEnv
                 ; case Map.lookup n env of
                     Just(ty@(polyk,mod,n,exp)) ->
                        case mod of
                          Wob -> return ty
                          Rig -> do { theta <- getBindings
                                    ; sig2 <- sub ([],theta,[],[]) polyk
                                    ; return(sig2,mod,n,exp)}
                     Nothing -> failD 2 [Ds "Not in scope: ", Dd n]}


ruleName (RW nm key rclass vars hyps lhs rhs) = nm

-------------------------------------------------------------------

underFrag cntxt frag comp = under frag cntxt (\ unifier -> comp)
underFragUsingTheta cntxt frag comp = under frag cntxt comp

under :: Frag -> (String,Rho) -> (Unifier -> TC a) -> TC a
under frag (p@(nm,rho)) comp =
  do { -- Set up the environment using the frag
       frag2@(Frag _ patVars _ eqs _ _ _) <- zonk frag
     ; env0 <- tcEnv
     ; (envVars,envTrip) <- getVarsFromEnv    -- Get vars before adding frag, for escape check
     ; env <- (addFragC nm frag2 env0)        -- Add frag info to get new env

     -- Run the computation (in the new env) and collect the predicates
     ; let u0 = bindings env
     --; warnM [Ds ("\nIn under "++nm),Ds "\nu0 = ", Dl u0 ",  "]                                        
     
     ;  (answer,collected) <- handleM 3 (collectPred (inEnv env (comp u0)))
                                        (underErr1 patVars)
     --; warnM [Ds("\nIn "++nm++" We collected "),Dl collected ";"]             
     ; ((levelvars,u5),unsolved,truths,need) <- solveConstraints p env (subPred u0 collected)
     ; equalityVarsGetBound u5 eqs
     ; rigidVarsEscape u5 eqs
     ; (bad,passOn) <- splitObligations unsolved patVars
     ; when (not (null bad))
            (failD 2
              [Ds "\nIn the scope of the patterns: ",Ds nm
              ,Ds "\nUnder the assumptions:\n   "
              ,Dl truths ", "
              ,Ds "\nWe could not solve the obligations:\n   "
              ,Dl need ", "
              ,Ds "\nBecause after simplification we were left with:\n   "
              ,Dl bad ", "])

     ; let (uVars,uTrip) = (map fst u5,uInfo u5)
           vars = envVars ++ uVars
           triples = envTrip ++ uTrip
     ; let bad = nub(filter (`elem` vars) patVars)
     ; when (not (null bad)) (escapes triples bad)
     ; injectA (" under "++nm++" ") passOn
     ; mutVarSolve u5  -- Permanently Bind any Flexi vars in the unifier
     --; warnM [Ds ("\nOut under "++nm++" pass on = ")
     --        ,Ds "\ncollected = ",Dd collected
     --        ,Dl passOn ";"]
     ; return answer
     }


-----------------------------------------------------------------
-- helper functions

describePat :: Pat -> IORef Rho -> IO String
describePat pat ref = do { r <- readIORef ref; arisesPat pat r}


-- arisesPat (Cons x xs) (Int -> [Int] -> [Int]) = an IO computation that returns
-- "(Cons x xs)::[Int] where
--    x::Int
--    xs::[Int]"

arisesPat ::Pat -> Rho -> IO String
arisesPat pat rho = do { r <- zonkRho rho; d <- readRef dispRef 
                       ; kindelems <- showKinds3 r
                       ; (c,args,d2) <- f pat r d []
                       ; let (d3,kindstrs) = displays d2 kindelems
                       ; writeRef dispRef d3
                       ; return("the pattern: "++c++"\nwhere pattern vars are typed as:"++concat (map h args)++kindstrs )}
  where h s = "\n   "++s
        f (Pcon v (p:ps)) (Rarrow dom rng) d args = f (Pcon v ps) rng d2 (arg:args)
            where(d2,arg) = displays d [Dd p,Ds "::",Dd dom]
        f (Pcon v (p:ps)) (Rtau (TyApp (TyApp (TyCon _ _ "(->)" _) dom) rng)) d args = f (Pcon v ps) (Rtau rng) d2 (arg:args)
            where(d2,arg) = displays d [Dd p,Ds "::",Dd dom]
        f p rho d args = return (c,reverse args,d2)
            where (d2,c) = displays d [Dd pat,Ds "::",Dd rho]
                    
testTau = tarr intT (tarr (tlist intT) (tlist intT))

ta = arisesPat (Pcon (Global "Cons") [Pvar (Global "x"),Pvar (Global "y")]) (Rtau testTau)

arises2 :: Sigma -> Rho -> IO String
arises2 expect rho = do { e <- zonkSigma expect; r <- zonkRho rho
                        ; kindelements <- showKinds2 r
                        ; disp <- readRef dispRef 
                        ; let (d2,c) = displays disp [Ds "the expected type: ",Dd e,Ds " rigidifys to ",Dd r,Dr kindelements]  
                        ; writeRef dispRef d2
                        ; return c}
                          
arises4 :: String -> Rho -> IO String
arises4 name rho = do { r <- zonkRho rho
                      ; kindelements <- showKinds2 r
                      ; disp <- readRef dispRef 
                        ; let (d2,c) = displays disp [Ds ("the prototype: "++name++"::"),Dd r,Dr kindelements]  
                        ; writeRef dispRef d2
                        ; return c}
                        
arises6 name rho (t@(Tv unq (Rigid q loc (s,ref)) k)) = do { writeRef ref comp; return t}
  where comp = do { r <- zonkG rho
                  ; kindelements <- showKinds2 r
                  ; disp <- readRef dispRef 
                  ; let (d2,c) = displays disp [Ds ("the prototype: "++name++"::"),Dd r,Dr kindelements]  
                  ; writeRef dispRef d2
                  ; return c}
arises6 name rho t = return t                       
                        
                        
pred2Pair (Equality x y) ans = (x,y):ans
pred2Pair (Rel t) ans = ans

underErr1 patvars message =
    do { (d1@(DI (pairs,bad,supply))) <- readRef dispRef
       ; failK "underErr1" 3 [Ds (newmessage pairs)]}
  where bad pairs = concat [ match dispv patv | dispv <- pairs, patv <- patvars]
        --match (m,freshname) (Tv n (Rigid Ex loc (s,ref)) k) | m==n = [(freshname,loc,s)] 
        match (ZTv (Tv m flav k),freshname) (Tv n (Rigid Ex loc (s,ref)) k2) -- USEREF
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

-- The unifier obtained by solving the obligations must be
-- consistent with the bindings in the Type Checking Env.
-- These come either from a prototype, or a GADT constructor.
-- If they're not consistent then the function less
-- general then the user declared.

equalityVarsGetBound unifier eqs = test bad
   where bad = [(v,old,new) | (v,old) <- (foldr acc [] eqs), (u,new) <- unifier, u==v]
         test [] = return ()
         test ((v,old,new):more) | old /= new =
            failD 3 [Ds "The type variable: ",Dd v,Ds " is used in a context that reqires it to be "
                     ,Dd new,Ds ".\nThe functions declared type is too general."]
         test (m:more) = test more
         acc (Equality (TcTv x) tau) ans = (x,tau):ans
         acc (Equality tau (TcTv x)) ans = (x,tau):ans
         acc x ans = ans

-- if one of the variables bound in the unifier is a RigidVar
-- that is mentioned in the Equalities, then the term is not
-- as polymorphic as required.

rigidVarsEscape unifier eqs = do { (free,_) <- get_tvs eqs; bad_rigid unifier (filter rigid free)}
 where bad_rigid [] free = return ()
       bad_rigid ((v,term):more) free | TcTv v /= term =
         case find (== v) free of
           Just (x@(Tv u (Rigid q loc info) k)) ->
              failD 3 [Ds "The type variable ",Dd x,Ds " is not polymorphic as declared."
                      ,Ds "\nContext requires that it have type ",Dd term,Ds ".\n"]
           Nothing -> bad_rigid more free
       bad_rigid (_:more) free = bad_rigid more free
       rigid (Tv u (Rigid _ _ _) k) = True
       rigid _ = False

-- The bindings in a unifier are turned into a triples data structure.
-- This helps make better error reporting. A triple binds the name
-- used in the source file, with the type it is bound to in the unifier.

uInfo unifier = map f unifier
  where f (v,tau) = (name v,simpleSigma tau,[v])
        name (Tv _ (Rigid All loc (s,ref)) k) = s
        name v = show v



underErr pat rules assump oblig s =
   failK "underErr" 2
     [Ds ("\nWhile type checking in the scope of:\n   "++pat)
     ,Ds "\nWe need to prove:\n   ",Dd oblig
     ,Dwrap 80 "From the truths:" assump ","
     ,Dwrap 80 "And the rules:" (map ruleName rules) ","
     ,Ds "\nBut, ",Ds s]

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
pushHints protos (Data loc b n nm sig vs cs ders exts) = Data loc b n nm (applyName protos nm) vs cs ders exts
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
       doOneTypeFun (t@(TypeFun loc nm (Just pt) ms)) =
          do { (nmSigmaType,monoKindAsTau,nmTypeKind,names) <- inferPolyPT [] pt
             ; let poly = K names (nmSigmaType)
                   getLevel (Star n) = n
                   getLevel _ = lv 1
             ; return (nm,TyCon Ox (getLevel monoKindAsTau) nm poly,poly) }

hasMonoTypeFun :: TcEnv -> [Dec] -> TC [(String,DefTree TcTv Tau)]
hasMonoTypeFun env [] = return []
hasMonoTypeFun env1 (dd@(TypeFun loc nm (Just pt) ms) : more) =
  do { (nmSigmaType,monoKind,nmTypeKind,names) <- inferPolyPT [] pt
     ; let polyt@(K _ (sigma)) = K names (nmSigmaType)
     ; clauses <- mapM (checkLhsMatch (type_env env1) sigma) ms
     ; let f d (ts,ps,t) = displays d [Dl ts ",",Ds " ----> ",Dd t]
     ; morepairs <- hasMonoTypeFun env1 more
     ; rule@(NarR(a,xs))  <- makeRule nm polyt clauses
     ; trees <- defTree rule 
     ; tree <- case trees of
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
     ; return(NarR(NTyCon s Ox (lv 1) k,zs)) }

-- check the lhs (i.e. {plus (S x) y} = ... ) of each match

checkLhsMatch :: ToEnv -> Sigma -> ([PT],PT) -> TC ([Tau],[Tpat],Tau)
checkLhsMatch current sigma (ps,rhs) =
  do { -- Fresh Instance of the type for every clause
       (vars,_,Rtau tau) <- unBindWith (\ x -> return "FlexVarsShouldNeverBackPatch6") newflexi sigma
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
     ; let (rhsFree,rhsLevels) = getFree [] rhs
           lhsFree = map (\ (nm,tau,kind) -> nm) (concat envs)
           f s = do { m <- newTau (MK (Star (lv 2)))
                    ; k <- newTau (MK m)
                    ; nm <- fresh; return (s,TyVar nm (MK k),poly (MK k))}
     ; additional <- mapM f (rhsFree \\ lhsFree)
     -- ; when (not (null additional)) (outputString ("Additional = "++show additional))
     ; let newenv = concat envs ++ current
     ; loc <- getLoc
     ; exts <- getSyntax
     ; lhsTau <- mapM (toTau (newenv,loc,exts,[])) (tail ps)
     ; lhsExps <- mapM (uncurry check) (zip lhsTau ks)
     ; rhsTau <- toTau (additional ++ newenv,loc,exts,[]) rhs
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
checkPTBndr current (y@(Tcon (tag@('`':cs)) xs),_) = return [] --TyCon sx _ "Tag" _) = return[]
checkPTBndr current (y@(Tcon c xs),k) =
  do {(tau,kind@(K lvs sigma)) <- getInfo y current c
     ; let check1 [] rng = return(rng,[])
           check1 (x:xs) (Karr m n) =
             do { env1 <- checkPTBndr current (x,m)
                ; (rng,env2) <- check1 xs n
                ; return(rng,env1++env2)}
           check1 (x:xs) kind = failD 1 [Ds "The type: ",Dd y,Ds " is not well kinded"]
     ; (preds,kind2) <-  instanTy lvs sigma
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

comp new old =
  case compose (Left new) (Left old) of
    Left u3 -> return u3
    Right _ -> fail "compose fails"

------------------------------------------------------------
-- Structured normalization

type Info = (FiniteMap String [RWrule],[(String,DefTree TcTv Tau)],[Pred])

push2 :: Unifier2 -> Info -> Info
push2 ([],[]) info = info
push2 u (rules,defs,truths) = (rules,defs,sub2Pred u truths)

infoRules :: Info -> FiniteMap String [RWrule]
infoRules (rules,defs,truths) = rules
infoTruths:: Info -> [Pred]
infoTruths (rules,defs,truths) = truths

normSimplyTrue :: Info -> Pred -> TC(Maybe(Unifier2))
normSimplyTrue info (Rel (TyApp (TyCon sx _ "Nat'" k) x)) = return(Just([],[]))
normSimplyTrue info (p@(Equality x y)) =
  do { ((x2,y2),s3) <- norm2Pair norm2Tau sub2Tau info (x,y)
     ; if x2 == y2
          then return (Just s3)
          else return Nothing
     }
normSimplyTrue info _ = return Nothing


normPreConds :: Info -> Bool -> [Pred] -> TC (Maybe Unifier2)
normPreConds info False _ = return Nothing
normPreConds info True [] = return(Just ([],[]))


normPreConds info True (p:ps) =
  maybeM (normSimplyTrue info p)
         (\ u1 -> maybeM (normPreConds (push2 u1 info) True ps)
                         (\ u2 -> return (Just (composeTwo u2 u1)))
                         (return Nothing))
         (maybeM (normIsAssumed (infoTruths info) p)
                 (\ u1 -> maybeM (normPreConds (push2 u1 info) True ps)
                                 (\ u2 -> return (Just (composeTwo u2 u1)))
                                 (return Nothing))
                 (return Nothing))



normIsAssumed:: [Pred] -> Pred -> TC(Maybe Unifier2)
normIsAssumed truths q =
  do { let matchFirst [] = return Nothing
           matchFirst (p:ps) =
              eitherM (matchPred p q) 
                      (\ unifier -> return(Just unifier))
                      (\ pairs -> (matchFirst ps))
     ; matchFirst truths }



normWithLemmas:: Info -> [(RWrule,(Bool,a,[Pred],Tau,Tau))] -> Tau -> TC(Maybe(Tau,Unifier2))
normWithLemmas info [] term = return Nothing
normWithLemmas info ((lemma,(commutes,vs,preds,lhs,rhs)):more) term =
  case match2 ([],[]) [(lhs,term)] of
    Just u1 -> 
               do { let rhs' = sub2Tau u1 rhs
                        preconds = (sub2Pred u1 preds)
                  ; verbose <- getMode "theorem" 
                  ; proceed <-
                       case commutes of
                         False -> return True
                         True -> let lhs' = sub2Tau u1 lhs
                                 in return(rhs' < lhs')
                  ; RankN.whenM (verbose && proceed)
                      [Ds ("\n*** Trying lemma '"++rname lemma++"' on term:\n   ")
                      ,Ds "[" ,Dl preconds ",",Ds "] => "
                      ,Dd term,Ds "  --->  ",Dd rhs']
                  ; maybeM (normPreConds info proceed preconds)
                           (\ u2 -> do { let u3 = composeTwo u2 u1
                                             new2 = sub2Tau u3 rhs'
                                       ; (new3,u4) <- norm2Tau (push2 u3 info) new2 -- rew result for additional changes
                                       ; let u5 = composeTwo u4 u3
                                       ; return (Just (new3,u5))})
                           (normWithLemmas info more term)}
    Nothing -> normWithLemmas info more term


normWithRules4Name:: Info -> Unifier2 -> String -> Tau ->
                    ((Tau,Unifier2) -> TC(Tau,Unifier2)) -> TC(Tau,Unifier2)
normWithRules4Name info u1 nm term noneApplyContinuation =
 do { let goodRules =
            case Map.lookup nm (infoRules info) of
              Nothing -> []
              Just ts -> filter isRewrite ts
          fresh x = do { info <- freshLemma x; return(x,info)}
    ; rs <- mapM fresh goodRules
    ; maybeM (normWithLemmas info rs term)
             ( \ (newer,u2) -> do { let u3 = composeTwo u2 u1
                                  ; norm2Tau (push2 u3 info) newer})
             (noneApplyContinuation(term,u1))
    }


norm2Tau:: Info -> Tau -> TC(Tau,Unifier2)
norm2Tau (i@(rules,defs,truths)) t =
  do { --verbose <- getMode "narrowing"
     -- ; whenM verbose [Ds "\nNormTau ",Dd t,Ds "\n  ",Dl truths "\n  "];
      norm2T i t }

norm2T:: Info -> Tau -> TC(Tau,Unifier2)
norm2T info (y@(TyVar nm k)) = return(y,([],[]))
norm2T info (app@(TyApp x y)) =
   case rootTau app [] of
     (c@(TyCon sx level_ nm k),args) ->
       do { (args2,unifier) <- norm2TauL info args
          ; let new = applyT (c:args2)
          ; normWithRules4Name (push2 unifier info) unifier nm new return}
     (f,args) -> do { (ts,u) <- norm2TauL info (f:args); return(applyT ts,u)}

norm2T info (TyCon sx l nm k) = return(TyCon sx l nm k,([],[]))
norm2T info (Star n) = return(Star n,([],[]))
norm2T info (Karr x y) =
   do { ((a,b),u) <- norm2Pair norm2Tau sub2Tau info (x,y); return(Karr a b,u)}
norm2T info (TyFun nm k xs) =
   do { (ys,unifier) <- norm2TauL info xs
      ; let new = (TyFun nm k ys)
            found (nm,tr) = return tr
            notFound = (failM 0 [Ds "2) Unknown type function: ",Ds nm])
      ; tree <- maybeM (defTreeInfo nm) found notFound
      ; normWithDefs (push2 unifier info) tree new
          (normWithRules4Name (push2 unifier info) unifier nm new return)
               -- (crossFertilize (push unifier info)))
      }
norm2T info (TcTv v) = return(TcTv v,([],[]))
norm2T info (TySyn nm n vs xs t) =
   do { (t':xs',u) <- norm2TauL info (t:xs); return(TySyn nm n vs xs' t',u)}
norm2T info (TyEx l) =
   do { (vs,(ps,body)) <- unwind l
      ; (body',u) <- norm2Tau info body
      ; return(TyEx(windup vs (ps,body')),u)}


normWithDefs:: Info -> (DefTree TcTv Tau) -> Tau -> TC(Tau,Unifier2) -> TC(Tau,Unifier2)
normWithDefs info (Leaf pat free lhs rhs) term next =
 do { (lhs2,rhs2) <- freshX (free,lhs,rhs)
    ; case match2 ([],[]) [(lhs2,term)] of
        Just unifier ->
           do { let rewritten = sub2Tau unifier rhs2
              ; verbose <- getMode "narrowing"  
              ; RankN.whenM verbose [Ds "\n2Norm ",Dd term, Ds " ---> ", Dd rewritten,Ds "; "]
              ; norm2Tau (push2 unifier info) rewritten }
        Nothing -> next }       
normWithDefs info (Branchx pattern path trees) term next = first trees term
  where first [] term = next
        first (t:ts) term = normWithDefs info t term (first ts term)




norm2Rho :: Info -> Rho -> TC(Rho,Unifier2)
norm2Rho info (Rtau x) = do { (a,u) <- norm2Tau info x; return(Rtau a,u) }
norm2Rho info (Rarrow s r) =
  do { (a,u1) <- norm2Sigma info s
     ; (b,u2) <- norm2Rho (push2 u1 info) (sub2Rho u1 r)
     ; let u3 = composeTwo u2 u1
     ; return(Rarrow a b,u3)}
norm2Rho info (Rpair s r) =
  do { (a,u1) <- norm2Sigma info s
     ; (b,u2) <- norm2Sigma (push2 u1 info) (sub2Sigma u1 r)
     ; let u3 = composeTwo u2 u1
     ; return(Rpair a b,u3)}
norm2Rho info (Rsum s r) =
  do { (a,u1) <- norm2Sigma info s
     ; (b,u2) <- norm2Sigma (push2 u1 info) (sub2Sigma u1 r)
     ; let u3 = composeTwo u2 u1
     ; return(Rsum a b,u3)}


norm2Pred :: Info -> Pred -> TC(Pred,Unifier2)
norm2Pred info (Equality x y) =
  do { ([a,b],u) <- norm2TauL info [x,y]; return(Equality a b,u)}
norm2Pred info (Rel t) =
  do { (a,u) <- norm2Tau info t; return(Rel a,u) }



---------------------------
norm2ForAllArgs info [] = return([],([],[]))
norm2ForAllArgs info ((nm,MK k,q):ts) =
  do { (k',u2) <- norm2Tau info k
     ; let f (nm,MK tau,q) = (nm,MK(sub2Tau u2 tau),q)
     ; (ts',u3) <- norm2ForAllArgs (push2 u2 info) (map f ts)
     ; let u4 = composeTwo u3 u2
     ; return((nm,MK k',q):ts',u4)}

norm2Sigma:: Info -> Sigma -> TC(Sigma,Unifier2)
norm2Sigma info (Forall xs) =
  do { (ys,(eqn,rho)) <- unwind xs
     ; (ys',u0) <- norm2ForAllArgs info ys
     ; (eqn',u1) <- norm2PredL (push2 u0 info) (sub2Pred u0 eqn)
     ; let u2 = composeTwo u1 u0
     ; (rho',u3) <- norm2Rho (push2 u2 info) (sub2Rho u2 rho)
     ; let u4 = composeTwo u3 u2
     ; return(Forall(windup ys' (eqn',rho')),u4)}


-- Lifting normalizing functions

liftNf:: (Info -> t -> TC(s,Unifier2)) -> t -> TC(s,Unifier2,[Pred])
liftNf f tau =
  do { env <- tcEnv
     ; truths <- getTruths
     -- ; warnM [Ds "The rules =\n  ",Dl (concat(map snd(Map.toList(rules env)))) "\n  "]
     ; (tau',unifier) <- f (rules env,tyfuns env,truths) tau
     ; return(tau',unifier,sub2Pred unifier truths)}

nfTau = liftNf norm2Tau
nfPredL = liftNf norm2PredL


-- Does a term normalize to a non-TyFun term, and not extend the refinement?

normTyFunTau :: Tau -> TC(Maybe Tau)
normTyFunTau (x@(TyFun _ _ _)) =
  do { ans <- nfTau x
     ; case ans of
        (TyFun nm k args,_,_) -> return Nothing
        (result,([],[]),_) -> return(Just result)
        _ -> return Nothing }
normTyFunTau _ = return Nothing

----------------------------------------------------------------
-- Normalizing structured objects like lists and pairs

norm2Pair:: (Info -> t -> TC(t,Unifier2)) -> (Unifier2 -> t -> t) -> Info -> (t,t)-> TC ((t,t),Unifier2)
norm2Pair f sub info (x,y) =
  do { (x',u2) <- f info x
     ; (y',u3) <- f (push2 u2 info) (sub u2 y)
     ; let u4 = composeTwo u3 u2
     ; return((x',y'),u4)}

norm2L:: (Info -> t -> TC(t,Unifier2)) -> (Unifier2 -> t -> t) -> Info -> [t] -> TC ([t],Unifier2)
norm2L f sub info [] = return([],([],[]))
norm2L f sub info (t:ts) =
  do { (t',u2) <- f info t
     ; (ts',u3) <- norm2L f sub (push2 u2 info) (map (sub u2) ts)
     ; let u4 = composeTwo u3 u2
     ; return(t':ts',u4)}

norm2PairL:: Info -> [(Tau,Tau)] -> TC ([(Tau,Tau)],Unifier2)
norm2PairL i ps = norm2L (norm2Pair norm2Tau sub2Tau) subPair i ps
  where  subPair u (x,y) = (sub2Tau u x,sub2Tau u y)

cross2PairL:: Info -> [(Tau,Tau)] -> TC ([(Tau,Tau)],Unifier2)
cross2PairL i ps = norm2L (norm2Pair crossThenNorm sub2Tau) subPair i ps
  where  subPair u (x,y) = (sub2Tau u x,sub2Tau u y)
         crossThenNorm i tau =
            do { (tau1,u1) <- crossF i tau
               ; if not(tau==tau1)
                     then do { (tau2,u2) <- norm2Tau i tau1
                             ; warnM [Ds "Cross Result\n  ",Dd tau,Ds " ===> ",Dd tau2]
                             ; return(tau2,composeTwo u2 u1)}
                     else return (tau1,u1)
               }

norm2TauL:: Info -> [Tau] -> TC ([Tau],Unifier2)
norm2TauL info ts = norm2L norm2Tau sub2Tau info ts

-- not quite a list since normPred:: Pred ->[Pred]
norm2PredL info [] = return([],([],[]))
norm2PredL info (t:ts) =
  do { (t',u2) <- norm2Pred info t
     ; (ts',u3) <- norm2PredL (push2 u2 info) (sub2Pred u2 ts)
     ; let u4 = composeTwo u3 u2
     ; return(removeCommonTyCon t' ++ ts',u4)}

--------------------------------------------------------------
-- Cross fertilization
-- If we know (Equal z {f x y}) and we have term with with subterms {f x y}
-- denoted: Term[{f x y}], then rebuild it as Term[z]

crossFertilize:: Info ->  (Tau,Unifier2) -> TC(Tau,Unifier2)
crossFertilize (info@(rules,defs,truths)) (term,u) = find truths
  where find [] = return (term,u)
        find ((t@(Equality x y)):ts) | (term==y) && (not(x == y)) =
              warnM [Ds "\nCross fertilizing with:\n  ",Dd t] >>
              norm2Tau (push2 u info) x
        find (t:ts) = find ts


-- Pushes "crossFertilize" into every subterm.
crossF info (y@(TyVar nm k)) = return(y,([],[]))
crossF info (app@(TyApp x y)) =
   do { ((a,b),u) <- norm2Pair crossF sub2Tau info (x,y)
      ; return(TyApp a b,u)}
crossF info (TyCon sx l nm k) = return(TyCon sx l nm k,([],[]))
crossF info (Star n) = return(Star n,([],[]))
crossF info (Karr x y) =
   do {((a,b),u) <- norm2Pair crossF sub2Tau info (x,y); return(Karr a b,u)}
crossF info (TyFun nm k xs) =
   do { (ys,unifier) <- norm2L crossF sub2Tau info xs
      ; let new = (TyFun nm k ys)
      ; crossFertilize (push2 unifier info) (new,unifier)}
crossF info (TcTv v) = return(TcTv v,([],[]))
crossF info (TySyn nm n vs xs t) =
   do { (t':xs',u) <- norm2L crossF sub2Tau info (t:xs)
      ; return(TySyn nm n vs xs' t',u)}
crossF info (TyEx l) =
   do { (vs,(ps,body)) <- unwind l
      ; (body',u) <- crossF info body
      ; return(TyEx(windup vs (ps,body')),u)}

-------------------------------------------------------------------

getLemmaRules nm =
  do { rules <- getMatchingRules isRewrite nm
     ; let fresh x = do { info <- freshLemma x; return(x,info)}
     ; rs <- mapM fresh rules
     ; return rs}

isAssumed:: Pred -> TC (Maybe Unifier2)
isAssumed q =
  do { truths <- getTruths
     ; let matchFirst [] = return Nothing
           matchFirst (p:ps) =
              eitherM (matchPred p q)
                      (\ unifier -> return(Just unifier))
                      (\ pairs -> (matchFirst ps))
     ; matchFirst truths }

matchPred :: Pred -> Pred -> TC (Either Unifier2 [(Tau,Tau)])
matchPred truth question =
  case work of
    Nothing -> return (Right [])
    Just pairs -> eitherM (mguB pairs)
                          (\ u -> return(Left u))
                          (\ _ -> return (Right pairs))
 where work = case (truth,question) of
                (Rel x,Rel y) -> Just [(x,y)]
                (TagNotEqual x y,TagNotEqual a b) -> Just[(x,a),(y,b)]
                (Equality x y,Equality a b) -> Just[(x,a),(y,b)]
                other -> Nothing





freshLemma :: RWrule -> TC (Bool,[(TcTv,Quant)],[Pred],Tau,Tau)
freshLemma r =
 do { info <- freshRule newflexi r
    ; case info of
       (commutes,vars,precond,Rel lhs,[Rel rhs]) -> return(commutes,vars,precond,lhs,rhs)
       -- BOGUS(commutes,vars,precond,Equality a b,[Equality x y]) -> return(commutes,vars,precond,teq a b,teq x y)
       _ -> failD 2 [Ds "In freshLemma ",Dd r,Ds " is not a lemma."]
    }


defTreeInfo s =
 do { table <- getTyFuns
    ; let p (nm,tree) = nm==s
    ; return (find p table)
    }


-- ====================================================================
-- Narrowing

help v term =
  do { (free,_) <- get_tvs term;
     ; return(if elem v free then [] else [(v,term)])}

pred2refine (Equality (TcTv (t@(Tv un (Rigid q loc nm) k))) y) = help t y
pred2refine (Equality y (TcTv (t@(Tv un (Rigid q loc nm) k)))) = help t y
pred2refine _ = return []

normUnder truths terms =
  do { refinement <- liftM concat (mapM pred2refine truths)
     ; terms' <- sub ([],refinement,[],[]) terms
     ; env <- tcEnv
     ; let env2 = env { bindings = composeMGU refinement (bindings env)
                      , assumptions = truths }
     ; whenM False -- (not (null terms))
             [Ds "\nNormalizing\n  ", Dl terms "\n  "]

     ; (ans,unifier,ts) <- inEnv env2 (liftNf norm2PairL terms')
     ; whenM False -- (not (null terms))
             [Ds "\nNormalized = \n  ",Dl ans "\n  "]
     ; inEnv (env2{assumptions = ts}) (liftNf cross2PairL ans)
     }


-- Here we assume the truths and the questions have already been normalized

solveByNarrowing :: (Int,Int) ->(String,Rho) -> [Pred] -> [(Tau,Tau)] -> TC Unifier2
solveByNarrowing (nsol,nsteps) context truths [] = return ([],[])
solveByNarrowing (nsol,nsteps) context@(s,_) normTruths tests =
    do { verbose <- getMode "narrowing"
       ; (free,levs) <- zonk (map (uncurry TyApp) tests) >>= get_tvs
       ; refinement <- getBindings
       ; whenM verbose
              [ Ds ("\n***********************\nIn solve: "++s)
              ,Ds "\nObligations = ",Dlf exhibitTT tests "; "
              ,Ds "\nTruths      = ",Dl normTruths "; "
              ,Ds "\nRefinement  = ",Dl refinement "; "];
       ; let ordered = sortBy lessTau tests
             conj = andP(map EqP ordered)
             hyp = andR(map EqR (foldr pred2Pair [] normTruths))
             originalVar (v,term) = elem v free

       ; reportEnter context tests conj normTruths
       ; (d2,cntxt) <- showThruDisplay [dProb conj]
       ; (ans2,(_,_,d3,exceed)) <- narr cntxt (nsteps,nsol,d2,False) [(conj,hyp,([],[]))] []
       ; let termOf (TermP x,ts,(ls,un)) = (x,(ls,un))
             termOf (EqP(x,y),ts,(ls,un)) = (teq x y,(ls,un))
       ; result <- if exceed
            then do {(solvedByDecProc) <- tryCooper (foldr pred2Pair [] normTruths) conj
                    ; if solvedByDecProc
                         then return([],[])
                         else failM 0 [Ds "Solving the equations: ",Dd tests
                                      ,Ds " exceeded narrowing resources."]}
            else case map termOf ans2 of
                  [(xinstan,(levelvars,unifier))] -> 
                     do { vs <- checkKind (filter originalVar unifier); return(levelvars,vs)}
                  [] -> failM 0 [Ds "The equations: ",Dd tests,Ds " have no solution"]
                  others -> moreThanOne context normTruths originalVar conj others
       ; reportExit result
       ; zonk2 result}

zonk2 (ls,vs) = do { ls' <- mapM f ls; vs' <- mapM g vs; return(ls',vs')}
  where f (x,y) = do { z <- zonkLv y; return(x,z)}
        g (x,y) = do { z <- zonk y; return(x,z)}

newToOld ex ans = (if ex then Exceeded else Answers)(map g ans)
  where g (TermP x,ts,(ls,un)) = (x,un)
        g (EqP(x,y),ts,(ls,un)) = (teq x y,un)

simplyTrue :: Pred -> TC (Maybe Unifier2)
simplyTrue (Rel (TyApp (TyCon sx _ "Nat'" k) x)) = return(Just ([],[]))
simplyTrue (p@(Equality x y)) =
  do { ((x2,y2),unifier,newTruths) <- liftNf (norm2Pair norm2Tau sub2Tau) (x,y)
     ; if x2 == y2
          then return (Just unifier)
          else return Nothing
     }
simplyTrue _ = return Nothing

moreThanOne context truths originalVar x others =
 do { solvedByDecisionProc <- tryCooper (foldr pred2Pair [] truths) x
    ; case (x,solvedByDecisionProc) of
        (_,True) -> return ([],[])
        (EqP(x,y),_) ->
            (maybeM (simplyTrue (Equality x y))
                    (\ u -> exit x (Just u))
                    (exit x Nothing))
        (other,_) -> exit x Nothing}
 where proj (t,(ls,u)) = (ls,filter originalVar u)
       short = map proj others
       contextElem (name,Rtau(Star LvZero)) =
           Ds ("While inferring the type for: "++name)
       contextElem (name,rho) =
           Dr [Ds ("\nWhile checking: "++name++":: "),Dd rho]
       exit origterm (Just u) = return u
       exit origterm Nothing = failM 2
          [contextElem context
          ,Ds "\nWe had to solve the narrowing problem:\n  "
          ,Dd origterm
          ,Ds "\nUnder the truths\n ",Dl truths "\n "
          ,Ds "\nBut, it has ambiguous solutions:\n  "
          ,Dl (map snd short) "\n  "]

-----------------------------------------------------------------
-- To solve by narrowing we need some helper functions


lessTau (x,y) (a,b) = compare (count a+count b) (count x+count y)
   where count (TyFun nm k xs) = 0
         count (TyCon sx _ nm k) = 2
         count (Star n) = 2
         count (TySyn nm n fs vs x) = count x
         count x = 1

reportEnter p conj normf truths =
 do { verbose <- getMode "narrowing"
    ; rs <- getLemmas
    ; normalString <- (renderProb (text "\nNormal form:" $$) normf)
    ; whenM verbose
         [Ds "\n####################c"
         ,Ds "\nSolve By Narrowing: ", Dd conj
         ,Ds "\nCollected by type checking in scope case ",Ds (fst p)
         ,Ds normalString
         ,Dwrap 80 "Assumptions: " truths ", "
         ,Dwrap 80 "   Theorems: " rs ", "]}

reportExit (levelvars,ans) =
 do { truths <- getAssume
    ; verbose <- getMode "narrowing"
    ; whenM verbose [Ds "\nAnswers = ", Dd ans,Ds "\nTruths = ",Dd truths]
    }

mentionsFree termL = ok
  where free = foldr union [] (map tvsTau (map (uncurry TyApp) termL))
        ok (v,term) = elem v free


checkKind [] = return []
checkKind ((v@(Tv n f (MK k)), term):more) =
  do { more' <- checkKind more
     ; (ws,_) <- get_tvs k  -- Get free vars in kind
     ; term' <- check term k
     ; return((v,term'):more') }


-- ====================================================================
-- Coopers Algorithm for solving Pressburger Arithmetic

tryCooper :: [(Tau,Tau)] -> Prob Tau -> TC Bool
tryCooper truths x =
  do { let xnorm = prob2Tau x
     ; (truthsnorm,_,_) <- liftNf norm2PairL truths
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

instance NameStore a => Exhibit a [Derivation] where
  exhibit d x = (d,render(PP.sep (map ppDeriv x)))

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
  exhibit d (Guarded xs) = (d,"No Guardeds yet")

instance  (NameStore a) => Exhibit a RuleClass where
  exhibit d x =(d,show x)

-----------------------------------------------------------------------
-- Translate a PT (the type that is parsed) into a Tpat. This is relatively
-- straightforward, the only difficult part is that every type application
-- must start with a TyCon, or it won't be a legitimate type-pattern
-- and that duplicate names (i.e. a var that appears twice in a pattern)
-- must map to the same Tvar for every occurrence.

pTtoTpat :: PT -> [(String,Tpat)] -> TC([(String,Tpat)],Tpat)
pTtoTpat (TyVar' s) env =
  case lookup s env of
    Nothing -> do { nm <- fresh; let u = Tvar s nm in return((s,u):env,u)}
    Just v -> return(env,v)
pTtoTpat (x@(TyApp' _ _)) e1 =
  do { let down (TyApp' (TyCon' s _) x) = return(s,[x])
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
pTtoTpat (TyCon' s _) e1 = return(e1,Tcon s [])  
pTtoTpat (Star' n Nothing) e1 = return(e1,Tstar (lv n))
pTtoTpat (Star' k (Just s)) env =
  case lookup s env of
    Nothing -> do { nm <- newLevel
                  ; let u = (Tstar (incLev k nm))
                  ; return((s,u):env,u)}
    Just(Tstar v) -> return(env,Tstar (incLev k v))
pTtoTpat (TyFun' (TyVar' s : xs)) e1 =
  do { (e2,ys) <- thrd e1 pTtoTpat xs
     ; return(e2,Tfun s ys) }
pTtoTpat (Ext ext) e1 =
  do { exts <- syntaxInfo
     ; loc <- currentLoc
     ; new <- buildExt (show loc) extToTpatLift ext exts
     ; pTtoTpat new e1
     }
pTtoTpat x e1 = fail ("The type: "++show x++" is not appropriate for the LHS of a type fun.")

thrd e1 f [] = return(e1,[])
thrd e1 f (x:xs) = do { (e2,y) <- f x e1; (e3,ys) <- thrd e2 f xs; return(e3,y:ys)}

----------------------------------------------------------------------
-- This code is used to translate a sigma type into a rule.
-- given (forall a . P a => T a -> S a -> Q a)
-- We need to test that T, S and Q are all Proposition constructors.
-- The rule would be  Q a -> T a, S a  When P a
-- we need to translate (Q a) into a pattern so that we can
-- match Propositions against it to obtain a binding for "a"
-- Rules are classifed as Axiom, BackChain (Rewrite or Refinement)
-- depending upon if the function is the type of a Constructor
-- function (Axiom) of a prop or if it is the type of a total
-- function (BackChain). Rewrite and Refinement are used for the theorem decl.

data RuleClass = Axiom | BackChain | Rewrite Bool | Refinement deriving Show


--               name   key    class     Vars                Precond Lhs  Rhs
data RWrule = RW String String RuleClass [(Name,Kind,Quant)] [Pred]  Pred [Pred]
--                                       Quant=Ex if Name not in LHS

axiom (RW nm key Axiom args precond lhs rhs) = True
axiom _ = False

rname (RW nm key rclass args precond lhs rhs) = nm
rkey  (RW nm key rclass args precond lhs rhs) = key
isRewrite (RW nm key (Rewrite b) vs pre lhs rhs) = True
isRewrite (RW nm key _ vs pre lhs rhs) = False

isBackChain (RW nm key BackChain vs pre lhs rhs) = True
isBackChain (RW nm key Axiom vs pre lhs rhs) = True
isBackChain (RW nm key _ vs pre lhs rhs) = False

isRefinement (RW nm key Refinement vs pre lhs rhs) = True
isRefinement (RW nm key _ vs pre lhs rhs) = False

zonkRW (RW nm key cl vs pre lhs rhs) =
  do { a <- zonk pre; b <- zonk lhs; c <- zonk rhs; return(RW nm key cl vs a b c)}

instance Zonk (Mtc TcEnv Pred) RWrule where
  zonkG (RW name key rclass args preCond lhs rhs)=
    do { let f (nm,k,q) = do { k2 <- zonkG k; return(nm,k2,q)}
       ; a2 <- mapM f args; p2 <- zonkG preCond
       ; l2 <- zonkG lhs; r2 <- zonkG rhs
       ; return(RW name key rclass a2 p2 l2 r2)}
  tvs f = error "No way to get the type vars from a RWrule"
 
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

-- ======================================================================
-- refinement lemma has one of the two the forms
-- 1)   cond1 -> ... -> condN -> Equal term1 term2 -> Equal var1 term3
-- 2)   cond1 -> ... -> condN -> Equal term1 term2 -> (Equal var3 term3, ... , Equal varN termN)
-- As a RWRule  (RW name key Refinement vars [cond1 ... condN]
--                           (Equal term1 term2)
--                           [Equal var3 term3, ... , Equal varN termN])
-- The effect is to replace the assumption (Equal term1 term2) with
-- the refinement [(var3,term3), ... , (varN,termN)]


refineEq (TyApp (TyApp (TyCon sx _ "Equal" k) (TyVar v k2)) t) vs = Just([Equality (TyVar v k2) t],vs)
refineEq (TyApp (TyApp (TyCon sx _ "(,)" k) x) y) vs =
  do { (xs,us) <- refineEq x vs; (ys,ws) <- refineEq y us; return(xs++ys,ws)}
refineEq (TyEx zs) vs =
  case unsafeUnwind zs of
    (us,([],base)) -> refineEq base (vs ++ us)
    (us,(preds,base)) -> Nothing
refineEq t vs = Nothing

refineP (TyApp (TyApp (TyCon sx _ "(->)" k) x) y) conds = refineP y (x:conds)
refineP last (lhs:conds) =
  do { (zs,vs) <- refineEq last []
     ; (c,a,b) <- equalPartsM lhs
     ; eqPred <- case c a b of
                 eq@(Equality _ _) -> Just eq
                 _ -> Nothing -- filter out TagNotEqual
     ; return(vs,reverse conds,eqPred,zs)}
refineP _ _ = Nothing

sigmaToRefinementRule name (Forall l) =
  case unsafeUnwind l of
    (vs,([],Rtau tau)) ->
      do { let g (nm,k,_) = (nm,k,Ex)
         ; (us,conds,lhs,pairs) <- refineP tau []
         ; return(RW name "Equal" Refinement (vs++map g us) (map makeRel conds) lhs pairs)}
    other -> Nothing


-- Given a set of truths, we refine a Frag by 1) trying all the refinement
-- Lemmas against the given truths and the equalities in the frag. 2) We add
-- these refinements to the frag, and 3) remove each equality from the frag
-- that led to a refinement.


freshRefinement :: RWrule -> TC ([(TcTv,Quant)],[Pred],(Tau,Tau),[Pred])
freshRefinement r =
 do { info <- freshRule newflexi r
    ; case info of
       (commutes,vars,precond,Equality a b,rhs) -> return(vars,precond,(a,b),rhs)
       _ -> failD 2 [Ds "In freshRefinement ",Dd r,Ds " is not a refinement lemma."]
    }

getRefinementRules newrules =
  do { rules <- getMatchingRules isRefinement "Equal"
     ; return (rules ++ (filter isRefinement (map snd newrules)))
     }

subT env t = sub ([],env,[],[]) t

commutingMatch (a,b) (x,y) =
  case match2 ([],[]) [(a,x),(b,y)] of
    Just u -> Just u
    Nothing -> match2 ([],[]) [(b,x),(a,y)]

establish :: Bool -> [Pred] -> TC(Maybe Unifier2)
establish False _ = return Nothing
establish True [] = return(Just ([],[]))
establish True (p:ps) =
  maybeM (simplyTrue p)
         (\ u1 -> maybeM (establish True ps)
                         (\ u2 -> do { let u3 = composeTwo u2 u1
                                     ; return (Just u3)})
                         (return Nothing))
         (maybeM (isAssumed p)
                 (\ u1 -> maybeM (establish True ps)
                                 (\ u2 -> do { let u3 = composeTwo u2 u1
                                             ; return (Just u3)})
                                 (return Nothing))
                 (return Nothing))


--; let fresh x = do { info <- freshRefinement x; return(x,info)}
--     ; rs <- mapM fresh (rules ++ (filter isRefinement (map snd newrules)))
--     ; return rs}

applyRefinements [] term = return Nothing
applyRefinements (lemma:more) (x,y) =
  -- warnM [Ds "\n",Dd lemma,Ds "\n(a,b) = ",Dd (a,b), Ds "\n(x,y) = ",Dd (x,y)] >>
  do { (vs,preds,(a,b),refinement) <- freshRefinement lemma
     ; case commutingMatch (a,b) (x,y) of
         Just (_,u1) -> 
                    do { new <- subT u1 refinement
                       ; let preconds = (subPred u1 preds)
                       ; verbose <- getMode "theorem"
                       ; whenM verbose
                           [Ds ("\n*** Trying refinement '"++rname lemma++"' on term:\n   ")
                           ,Ds "[" ,Dl preconds ",",Ds "] => "
                           ,Dd (Equality x y),Ds "  --->  ",Dd new
                           ]
                       ; maybeM (establish True preconds)
                          (\ u2 -> do { let u3 = composeTwo u2 ([],u1)
                                            ans = sub2Pred u3 refinement
                                      ; return(Just(u3,ans))})
                          (applyRefinements more (x,y))}
         Nothing -> applyRefinements more (x,y)}

extendEqsWithRules :: [RWrule] -> [Pred] -> [Pred] -> TC[Pred]
extendEqsWithRules rules [] new = return new
extendEqsWithRules rules (p:ps) new =
   case p of
    (Equality x y) -> maybeM (applyRefinements rules (x,y)) next1 next2
    (Rel t) -> next2
  where next1 (u,ok) =
          do { let new2 = sub2Pred u new
                   [p2] = sub2Pred u [p]
             ; extendEqsWithRules rules (nub(ps ++ok)) (p2 : new2)}
        next2 = extendEqsWithRules rules ps (p : new)

--------------------------------------------------------
-- refineFrag puts a frag in normal form before it is
-- added to the environment.
-- 1) It normalizes assumptions
-- 2) It removes common constructors from Eqalities
--    i.e. [Equal (T x y) (T a b)] --> [Equal x a,Equal y b]
-- 3) extends the refinement by applying applicable refinement lemmas


refine refinement eqs newRules =
  do { rules <- getRefinementRules newRules
     ; outerTruths <- getTruths
     ; (normTruths,_,_) <- underRules newRules (liftNf norm2PredL eqs)
     ; newEqs <- extendEqsWithRules rules normTruths []
     ; let (pairs,truths) = split newEqs [] []
     ; newRefine <- comp pairs refinement
     {-
     ; warnM [Ds "\nNew refinement = ",Dl pairs ", "
                  ,Ds "\nNew truths = ",Dl truths "; "
                  ,Ds "\nNormtruths = ",Dl normTruths "; "
                  ,Ds "\nOuter facts = ",Dl outerTruths "; "
                  ,Ds "\nrules = ",Dl (map fst rules) "; "]
     ; whenM (not (null pairs)) [Ds "\nRefinement lemma adds extension: ",Dl pairs ", "]
     -}
     ; return(nub newRefine,truths)}


-- preds and qs start out identical, as we accumulate the refinement
-- we apply the refinement to preds, so it propagates, but we don't want it to
-- accumulate in truths, so when it's not a refinement we put q on truths

split ((Equality (TcTv v@(Tv un (Rigid _ _ _) k)) y):preds) refine truths =
    split (subPred [(v,y)] preds) ((v,y):refine) truths
split ((Equality y (TcTv v@(Tv un (Rigid _ _ _) k))):preds) refine truths =
    split (subPred [(v,y)] preds) ((v,y):refine) truths
split ((Equality x y):pred) refine truths | x==y = split pred refine truths
split (p:preds) refine truths = split preds refine (p:truths)
split [] refine truths = (refine,truths)


-- Equal (T x a) (T y b) --> [Equal x y,Equal a b]
removeCommonTyCon (Equality x y) = temp x y
removeCommonTyCon x = [x]

temp:: Tau -> Tau -> [Pred]
temp (m@(TyApp f x)) (n@(TyApp g y)) =
  case (rootConst m [],rootConst n []) of
    (Just(nm1,ts1),Just(nm2,ts2))
        | (nm1==nm2) && (length ts1)==(length ts2) -> concat (zipWith temp ts1 ts2)
    (Just(nm1,ts1),Just(nm2,ts2))
        | rigid nm1 && rigid nm2 && (length ts1)==(length ts2) -> (Equality nm1 nm2): concat (zipWith temp ts1 ts2)
    other -> [Equality m n]
temp x y = [Equality x y]

rigid (TcTv (Tv un (Rigid _ _ _) k)) = True
rigid x = False

rootConst (TyApp f y) ys = rootConst f (y:ys)
rootConst (t1@(TyCon sx level nm k)) ys = return(t1,ys)
rootConst (t1@(TcTv (Tv un (Rigid _ _ _) k))) ys = return(t1,ys)
rootConst (t1@(TcTv (Tv un (Skol _) k))) ys = return(t1,ys)
rootConst _ _ = fail "Not an application of a TyCon"

-- ======================================================================
-- Given a set of truths and a set of predicates that ALL need to be
-- solved, If we can unify any of the predicates with a truth we can
-- remove it from the predicates needing solution. This makes the set
-- of things that must ALL be true smaller, But for each unification
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


elim n [] = []
elim 0 (x:xs) = xs
elim n (x:xs) = x : (elim (n-1) xs)


truthStep2 :: TyCh m => ([Tau],[Tau],[String],Unifier2) -> m[([Tau],[Tau],[String],Unifier2)]
truthStep2 (truths,questions,open,u0) = 
     do { pairs <- mapM run pairsM
        ; return $ sortBy moreGeneral 
                 $ relevant 
                 $ sortBy samePred
                 [ (map (sub2Tau u) truths
                   , map (sub2Tau u) (elim n questions)
                   , open,composeTwo u u0
                   ,n)
                 | (n,[u]) <- pairs ]
       }
  where unifyM :: TyCh m => [(Tau,Tau)] -> m[Unifier2]
        unifyM xs = eitherM (mguB xs) (\ ans -> return[ans]) (\ _ -> return[])
        run (n,x) = do { a <- x; return(n,a)}
        pairsM = [ (n,unifyM [(t,q)])
                 | t <- truths
                 , (q,n) <- zip questions [(0::Int)..]
                 ]
        samePred (ts1,ps1,_,(_,u1),i) (ts2,ps2,_,(_,u2),j) = compare (i,length u1)(j,length u2) 
        relevant [] = []
        relevant [(t,p,s,u,i)] = [(t,p,s,u)]
        relevant (x@(_,_,_,(_,[]),i):y@(_,_,_,_,j):zs) | i==j = relevant (x:zs)
        relevant ((t,p,s,u,i):zs) = (t,p,s,u):relevant zs
        moreGeneral (ts1,ps1,_,(_,u1)) (ts2,ps2,_,(_,u2)) = compare (length u1)(length u2)


      

---------------------------------------------------------------

ruleStep :: ([Tau],[Tau],[String],Unifier2) -> TC(Maybe[([Tau],[Tau],[String],Unifier2)])
ruleStep (truths,[],open,u0) = return (Nothing)
ruleStep (truths,q:questions,open,u0) =
   do { s <- predNameFromTau q q
      ; rules <- getMatchingRules isBackChain s
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
                  ; let f13 q (ts,qs,nms,u) = (ts,(sub2Tau u q):qs,nms,u)
                  ; return(fmap (map (f13 q)) zs)}
         ws -> do { good <- foldM goodMatch [] ws
                  ; let fixform (newtruths,rhs,nms,u) =
                          (newtruths,rhs ++ fix questions,nms,composeTwo u u0)
                           where fix x = map (sub2Tau u) x
                  ; return(Just(map fixform good))}}



goodMatch good (truths,precond,result,open,unifier) =
  do { ans <- solv 4 [(truths,map (unRel 5) precond,open,unifier)]
     ; case ans of
         [(truths2,[],nms,u)] -> return((truths2,map (sub2Tau u) (map (unRel 6) result),open,u):good)
         _ -> return good}

unRel n (Rel x) = x
unRel n x = error ("\nunRel applied to non Rel: "++show x++" "++show n)

exploreD n = length n > 3


-- Does any rule match term?
matchR ::[Tau] -> [String] -> [RWrule] -> Tau -> TC[([Tau],[Pred],[Pred],[String],Unifier2)]
matchR truths openRules [] term = return []
matchR truths open ((r@(RW nm key BackChain _ _ _ _)):rs) term
  | elem nm open = matchR truths open rs term
matchR truths open ((r@(RW nm key _ _ _ _ _)):rs) term
  | exploreD (filter (nm==) open) = matchR truths open rs term
matchR truths open ((r@(RW nm key cl _ _ _ _)):rs) term =
  do { (commutes,vars,precond,Rel lhs,rhs) <- freshRule newflexi r
     ; ys <- matchR truths open rs term
     ; maybeM (mostGenUnify [(lhs,term)])
        (\ sub ->    do { let pre2 = sub2Pred sub precond
                              rhs2 = sub2Pred sub rhs
                        ; verbose <- getMode "solving"
                        ; whenM verbose
                            [Ds "\nRule : ",Ds nm
                            ,Ds "\nMatched term: ",Dd term
                            ,Ds "\n Rewrites to: ",Dd rhs2
                            ,Ds "\n Under subst: ",Dd sub
                            ,Ds "\nPrerequisite: ",Dd pre2]
                        ; return((map (sub2Tau sub) truths,pre2,rhs2,nm:open,sub):ys) })
        (return ys)
     }

----------------------------------------------------------------------------
-- Solving a list of predicates returns a second list of, hopefully,
-- simpler predicates. If the returned list is empty, then the input
-- is solved.

solveConstraints :: ([Char],Rho) -> TcEnv -> [Pred] -> Mtc TcEnv Pred (Unifier2,[Pred],[Tau],[Tau])
solveConstraints (nm,rho) env collected =
  do { -- Split into Equalities and Relations, and normalize everything.
     -- ; warnM [Ds "\nsolve Con\n  ",Dl collected "\n  "]
     ; let (oblig,residualNonEqRels) = splitR collected ([],[])
           assump = assumptions env -- Truths stored in the extended environment
           rules = getRules "" env
     ; (truths1,u0,_) <- inEnv env (liftNf norm2PredL assump)
     ; let oblig2 = foldr pred2Pair [] (sub2Pred u0 oblig)
     ; (normOblig,u1,normTruths) <- inEnv env (normUnder truths1 oblig2)
     ; steps <- getBound "narrow" 25
     ; u2 <- handleM 2
                  (inEnv env (solveByNarrowing (3,steps) ("9."++nm,rho) normTruths normOblig))
                  (\ message -> 
                      do { ans <- mguB oblig2
                         ; warnM [Ds "Trying simple unification, "]
                         ; case ans of
                             Left unifier2 -> warnM [Ds "which succeeds: ",Dd unifier2] >>
                                              return unifier2
                             Right(m,_,_) -> warnM [Ds "which fails: ",Ds m] >>
                                             underErr nm rules assump oblig message})
     ; let u3 = composeTwo u2 (composeTwo u1 u0)
     ; expandTruths <- inEnv env (expandTruths2 (sub2Pred u3 normTruths))
     ; (residual',u3b,_) <- liftNf norm2TauL residualNonEqRels -- Normalize residual constraints
     ; let u3c = composeTwo u3 u3b
     ; (unsolved,un4) <- inEnv env (solvP expandTruths (map (sub2Tau u3c) residual'))
     ; let u5 = composeTwo un4 u3c
     ; let truths = (map (sub2Tau u5) expandTruths)
           need = (map (sub2Tau u5) residualNonEqRels)
     ; return(u5,unsolved,truths,need)}

splitR [] (eqs,rels) = (eqs,rels)
splitR ((p@(Equality _ _)):ps) (eqs,rels) = splitR ps (p:eqs,rels)
splitR ((Rel t):ps) (eqs,rels) = splitR ps (eqs,t:rels)

splitR' [] (eqs,rels) = (eqs,rels)
splitR' ((p@(Equality x y)):ps) (eqs,rels) = splitR' ps ((x,y):eqs,rels)
splitR' ((Rel t):ps) (eqs,rels) = splitR' ps (eqs,Rel t:rels)

--               Truths Quest Rules
solv :: Int -> [([Tau],[Tau],[String],Unifier2)] -> TC ([([Tau],[Tau],[String],Unifier2)])
solv n [] = return ([])
solv 0 xs = warnM [Ds "\nThe 'backchain' bounds have been exceeded."] >> return ([])
solv n ((ts,[],nms,u):xs) =
  do { (ys) <- solv (n-1) xs
     ; return ((ts,[],nms,u):ys) }
solv n ((x@(ts,qs,nms,u)):xs) =
  do { ans <- truthStep2 x
     ; case ans of
        [] -> do { m <- ruleStep x
                 ; case m of
                     Nothing -> do { (ys) <- solv (n-1) xs; return(x:ys)}
                     Just ws ->  solv n (xs++ws) }
        zs -> do { whenM False [Ds "Truth Steps\n  ",Dlf f15 zs "\n  "
                               ,Ds "\n questions = ",Dl qs "; "
                               ,Ds "\ntruths = ",Dl ts "; "]
                 ; solv n (zs++xs)}}

f15 d (ts,qs,_,u) = displays d [Ds "[",Dl ts ",",Ds "] => [",Dl qs ",",Ds"]", Ds " where ",Dd u]

solvP :: [Tau] -> [Tau] -> TC([Pred],Unifier2)
solvP truths questions =
  do { steps <- getBound "backchain" 4
     ; ans <- solv steps [(truths,questions,[],([],[]))]
     ; let aMostGeneral (ts,qs,nms,(levelu,u)) = null u
           axiom [] = False
           axiom (c:cs) = isUpper c
           axiomOnlySolution (ts,qs,nms,u) = all axiom nms
           ambig preds = failM 2 [Ds "Ambiguous solutions to: ["
                                 ,Dl truths ",",Ds "] => ["
                                 ,Dl questions ",",Ds "]\n   "
                                 ,Dlf (showOneAmbig questions) preds ""]
           nosols = failD 3 [Ds "No solution to [",Dl truths ", ",Ds "] => [", Dl questions ",",Ds "]"]
     ; unique ans
         (nosols)                                        -- None
         (\ (ts,qs,nms,u) -> return(map makeRel qs,u))   -- Exactly One
         (eitherM (allRefutable ans)                     -- Many
                  (\good -> case (find aMostGeneral good) of
                             Just(ts,qs,nms,u) -> return(map makeRel qs,u)
                             Nothing ->
                                 (unique (filter axiomOnlySolution good)
                                         (ambig good)                  -- NONE
                                         (\ (ts,qs,nms,u) ->
                                            return(map makeRel qs,u))  -- Exactly One
                                         (ambig good)))                -- MANY
                  (\ elem -> failM 2 [Ds "\nThere is no solution to ["
                                     ,Dl questions ", ",Ds "] because"
                                     , elem]))
     }

unique x none onef many =
  case x of
   [] -> none
   [ans] -> onef ans
   (y:ys) -> many

-- Given an ambiguous list of solutions to some questions, some may be
-- refutable, so we should filter them out. If all are refutable, then
-- the questions themselves are refutable.

allRefutable :: [([Tau],[Tau],[String],Unifier2)] -> TC(Either [([Tau],[Tau],[String],Unifier2)] (DispElem Z))
allRefutable sols = do { xs <- mapM test1 sols; check xs sols []}
 where test1 (truths,quests,names,unifier) = refutable (map Rel quests)
       check [] sols good = return(Left good)
       check (Nothing : xs) (s:sols) good = check xs sols (s:good)
       check (Just dispElem : xs) sols good = return(Right dispElem)


showOneAmbig term d (ts,ps,nms,(levelu,u)) = displays d [Ds "\n   ",Dd (subPred u (map Rel term))]
g45 d (ts,ps,nms,u) = displays d [Ds "questions [",Dl ps ",",Ds "] unifier ",Dd u,Ds " rules used ",Dl nms ","]


expandTruths2 truths =
  do { let (eqs,rels) = splitR truths ([],[])
     ; zss <- mapM expandTau rels
     ; let ans = nub(concat zss)
     ; return(ans++map pred2Tau eqs)
     }

expandTau truth =
   do { s <- predNameFromTau truth truth
      ; rules <- getMatchingRules isBackChain s
      ; checkTau rules truth
      }

checkTau :: [RWrule] -> Tau -> TC [Tau]
checkTau [] truth = return [truth]
checkTau ((r@(RW nm key (Rewrite b) _ _ _ _)):rs) truth = checkTau rs truth
checkTau ((r@(RW nm key BackChain _ _ _ _)):rs) truth = checkTau rs truth
checkTau ((r@(RW nm key Refinement _ _ _ _)):rs) truth = checkTau rs truth
checkTau ((r@(RW nm key Axiom _ _ _ _)):rs) truth =
  do { (commutes,vars,precond,Rel lhs,rhs) <- freshRule newflexi r
     ; ys <- checkTau rs truth
     ; case match2 ([],[]) [(lhs,truth)] of
        Just unifier -> do { let rhsts = map (unRel 33) rhs
                                 new = map (sub2Tau unifier) rhsts
                           ; verbose <- getMode "solving"
                           ; whenM verbose [Ds ("Axiom "++nm++" expands truths by:\n  "),Dl new "\n  "]
                           ; return(new ++ ys)}
        Nothing -> return ys }


-- =================================================================
-- effect free unifiers and their operations

mguWithFail:: TyCh m => [(Tau,Tau)] -> m [(TcTv,Tau)]
mguWithFail xs =
  eitherM (mguB xs)
          (\ (_,sub) -> return sub)
          (\(mess,t1,t2) -> fail mess)


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

mergeMgu :: TyCh m => [(TcTv,Tau)] -> [(TcTv,Tau)] -> m(Either [(TcTv,Tau)] (String,Tau,Tau))
mergeMgu sub1 sub2 =
  case findCommon sub1 sub2 of
   (_,_,[]) -> return(Left(composeU sub1 sub2))
   (sub1',sub2',triples) ->
      let project1(v,t1,t2) = (t1,t2)
          project2 sub (v,t1,t2) = (v,subTau sub t2)
      in eitherM (mguB (map project1 triples)) 
           (\ (_,sub3) -> eitherM (mergeMgu sub3 (composeU sub1' sub2'))
                             (\ us -> return(Left(us ++ map (project2 sub3) triples)))
                             (\ x -> return(Right x)))
           (\ x -> return(Right x))                            

{-      
      case mgu (map project1 triples) of
           Right x -> Right x
           Left(_,sub3) -> case mergeMgu sub3 (composeU sub1' sub2') of
                            Left us -> Left(us ++ map (project2 sub3) triples)
                            Right x -> Right x
-}

a1 = [("a",12),("b",34),("c",23)]
a2 = [("z",1),("a",22),("c",11),("e",99)]

-- =====================================================
-- Display, Exhibit, and Show of datatypes in Infer2
-- To Display a name, prints it in a more concise manner by
-- maintaining a list of concise names for each Var encountered.


{-
instance NameStore d => Exhibit d [(Var,(Sigma,CodeLevel,Exp))] where
  exhibit xs [] = (xs,"")
  exhibit xs ys = exhibitL exhibit xs ys "\n   "

instance NameStore d => Exhibit d (Var,(Sigma,CodeLevel,Exp)) where
  exhibit xs (v,(s,l,e)) = (zs,show v++": "++ans)
   where (zs,ans) = exhibit xs s

instance Exhibit (DispInfo Z) (Exp,Tau) where
  exhibit d1 (e,x) = displays d1 [Dd e, Ds ":: ",Dd x]
-}

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
  exhibit d1 (ExtP ep) = (d1,show ep)

instance  NameStore d => Exhibit d Var where
  exhibit d1 v = (d1,show v)

instance Exhibit (DispInfo Z) [String] where
  exhibit d1 s = (d1,plist "[" s "," "]")

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
  exhibit d (RW nm key (Rewrite b) vars pre lhs [rhs]) =
    displays d [Ds "Rewrite ", {- Dl vars ",", -}  Ds (nm++"("++key++"): ")
               ,Ds "[", Dl pre ", ", Ds "] => "
               ,Dd lhs,if b then Ds " -C-> " else Ds " --> ",Dd rhs]
  exhibit d (RW nm key rclass vars pre lhs rhs) =
    displays d [Ds (show rclass++" "++nm++"("++key++"): ")
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
   = (d3,blanks n ++"Leaf " ++ lhsX++ " --> "++ rhsX)
     where (d2,lhsX) = exhibit d1 lhs
           (d3,rhsX) = exhibit d2 rhs
           -- (d4,ff) = exhibitL exhibit d3 free ""
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

trans0 s = (readName "In trans0: ") (typeConstrEnv0,Z,[],[]) s

toEnvX :: ToEnv
toEnvX =
  [( "[]",        listT, poly star_star)
  ,( "(,)",       pairT, poly (karr star (star_star)))
  ,( "()",        unitT, poly star)
  ,( "(->)",      arrowT, poly (karr star (star_star)))
  ,( "Atom",      atomT, kind4Atom)
  ,( "(+)",       sumT, poly (karr star (star_star)))
  ,( "(!=)",      notEqT, notEqKind)
  ,( "DiffLabel", tyconDiffLabel, polyDiffLabel)
  ,( "String",    stringT, poly star)
  ,( infixEqName, TyCon Ox (lv 1) infixEqName equalKind, equalKind)
  --  ,( "Hidden",    hiddenT, kind4Hidden)
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
 "prop DiffLabel (t :: Tag) (t :: Tag) = primitive\n"++
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
 " deriving Nat(t)\n"++
 "prop Nat' :: Nat ~> *0 where\n"++
 "  Z:: Nat' Z\n"++
 "  S:: forall (a:: Nat) . Nat' a -> Nat' (S a)\n"++
 " deriving Nat(v)\n"++
-- "data Equal :: forall (a:: *1) . a ~> a ~> *0 where\n"++
-- "  Eq:: forall (b:: *1) (x:: b) . Equal x x\n"++

 "data Equal:: a ~> a ~> *0 where\n"++
 "  Eq:: Equal x x\n"++

 "data HiddenLabel :: *0 where\n"++
 "  HideLabel:: Label t -> HiddenLabel\n"++
 "data Row :: a ~> b ~> *1 where\n"++
 "  RNil :: Row x y\n"++
 "  RCons :: x ~> y ~> Row x y ~> Row x y\n deriving Record(r)\n"++
 "data Record :: Row Tag *0 ~> *0 where\n"++
 "   RecNil :: Record RNil\n"++
 "   RecCons :: Label a -> b -> Record r -> Record (RCons a b r)\n"++
 " deriving Record()\n"++
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
  do { (env2,ds2,_) <- checkDecs env ds
     ; rt_env <- elaborate None ds2 (runtime_env env2)  -- evaluate the list
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
 where body = do { PureReadline.setCompletionEntryFunction(return . expandTabs)
                 ; s <- PureReadline.readline prompt
                 ; let addHist Nothing = return ""
                       addHist (Just "") = return ""
                       addHist (Just s) = (PureReadline.addHistory s)>>(return s)
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
        reset ((ZInteger n,s):xs) =
          do { ys <- reset xs
             ; return((ZInteger n,s):ys)}
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



commandString =
 ":set p     set 'p' (e.g. :set solve, :set pred, :set narrow, :set kind, or :set theorem)\n"++
 ":q         quit\n"++
 ":rules     list rules in scope\n"++
 ":h         hint. What is the current expected type\n"++
 ":k t       print the kind of 't'\n"++
 ":t e       print the type of 'e'\n"++
 ":try e     match the type of 'e' against the expected type\n"

checkReadEvalPrint :: (Expected Rho,TcEnv) -> TC Bool
checkReadEvalPrint (hint,env) =
  do { let tabExpandFun = completionEntry env
     ; input <- getS "check> " tabExpandFun
     ; z <- parseString pCommand input
     ; case z of
        Left s -> do {putS s; return (True) }
        Right(x,rest) ->
         case x of
          (ColonCom "?" _) -> warnM [Ds commandString] >> return True
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
                ; putS (x++" :: "++(pprint k)++
                        "\n" ++ pprint t ++ "\n"++tree)
                ; return (True) }
          (ColonCom "t" x) ->
             case getVar (Global x) env of
                Just(sigma,mod,lev,exp) ->
                   do { s1 <- zonk sigma
                      ; updateDisp
                      ; warnM [Ds (x ++ " :: "),Dd s1]
                      ; verbose <- getMode "kind"
                      ; when verbose (showKinds varsOfPoly s1)
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
                ; ((ty::Rho,_),oblig) <- collectPred (infer exp)
                ; obs <- zonk oblig
                ; typ <- zonk ty
                ; updateDisp
                ; expect <- case hint of
                             Check rho -> zonk rho
                             Infer _ -> failD 1 [Ds "Can't try and match an expression against expected type if expected type is infer."]
                ; (vs,_) <- get_tvs expect
                ; eitherX <- morepolyRR vs typ expect
                ; case eitherX of
                   Left(unifier,preds) ->  
                      do { (u2@(_,unifier2),preds2) <- solveByUnify unifier preds
                         ; warnM [Ds(show exp ++ " :: "),Dd (sub2Rho u2 typ)]
                         ; warnM [Ds "\nUnder the refinement:\n  ",Dl unifier2 "\n  "]
                         ; warnM [Ds "\nOnly when we can solve\n  ",Dl (subPred unifier (obs++preds2)) "\n  "]
                         }
                   Right(message,t1,t2) ->
                      warnM [Ds "\nThe typing ",Dd exp, Ds " :: ",Dd ty
                            ,Ds "\ndoes not match the expected type:\n  ",Dd expect
                            ,Ds "\nBecause: ",Ds message,Ds "\n  "
                            ,Dd t1, Ds " =/= ",Dd t2]
                ; return True
                }
          (ExecCom exp) ->
             do { ((t,e2),oblig) <- collectPred (inferExp exp)
                ; t2 <- zonk t
                ; obs <- zonk oblig
                ; (u2@(_,unifier2),preds2) <- solveByUnify [] oblig
                ; let t3 = sub2Rho u2 t2
                ; updateDisp
                ; warnM [Ds(show exp ++ " :: "),Dd t3]
                ; verbose <- getMode "kind"
                ; when verbose (showKinds varsOfRho t3)
                ; whenM (not (null preds2)) [Ds "Only when we can solve\n   ",Dd preds2]
                ; return (True)
                }
          EmptyCom -> return True
          other -> putS "unknown command" >> return (True)
     }

checkLoop :: Expected Rho -> TcEnv -> TC ()
checkLoop typ env = interactiveLoop checkReadEvalPrint (typ,env)


solveByUnify :: TyCh m => Unifier -> [Pred] -> m (Unifier2,[Pred])
solveByUnify unifier preds = do { ans <- mguB eqs; return(combine ans)}
  where (eqs,rels) = splitR' preds ([],[])
        combine (Left u2) = let u3 = composeTwo u2 ([],unifier)
                            in (u3,sub2Pred u3 rels)
        combine (Right _) = (([],unifier),preds)
                         
                                                     
                                                     
-- ==================================================================
-- The Circuit extension

tcCircuit vs e ds expect =
 do { allOk ds
    ; (frag,ds2) <- inferBndrForDecs "where" localRename ds
    ; outputString ("\n\n"++show (Circ vs e ds)++"\n translates to \n")
    ; Frag env skols ts eqns theta rs exts <- zonk frag
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
-- which has the intermediate form:
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

hasMonoType (var,(K _ (Forall (Nil ([],Rtau t))),mod,_,_),mode) = return (var,t)
hasMonoType (var,x,mode) = fail (show var++" does not have a monomorphic type")

transForm (v,TyApp (TyCon sx l "Exp" k) t) = return ("Exp1",v,toRep t)
transForm (v,TyApp (TyApp (TyApp (TyCon sx l "Exp" k) c) row) t) = return ("Exp3",v,toRep t)
transForm (v,TyApp (TyCon sx l "Sig" k) t) = return ("Sig1",v,toRep t)
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

toRep (TyCon sx l "Bit" k) = Var (Global "Bit")
toRep (TyCon sx l "Int" k) = Var (Global "Int")
toRep (TyCon sx l "Z" k) = Var (Global "Z")
toRep (TyApp (TyCon sx l "S" k) x) = App (Var (Global "S")) (toRep x)
toRep (TyApp (TyApp (TyCon sx l "(,)" k) x) y) =
  (App (App (Var (Global "Prod")) (toRep x)) (toRep y))
toRep (TyApp (TyApp (TyCon sx l "Vec" k) x) y) =
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
  | LeftToRight ([(Name,Kind,Quant)],String,[Pred],Tau,Tau)
  | NotATheorem [Tau]

whatKind :: Maybe RuleClass -> Rho -> TC TheoremSplit
whatKind thclass rho =
  do { (doms,rng) <- rhoArrowParts rho
     ; let mkEx (nm,k,_) = (nm,k,Ex)
     ; case baseIsEquality rng [] of
         Just(vs,x,y) ->
            case (x,rootT x []) of
             (TyFun f _ _, any) -> return(LeftToRight(map mkEx vs,f,map makeRel doms,x,y))
             (any,Just(sx,lv,f,k,zs)) -> return(LeftToRight(map mkEx vs,f,map makeRel doms,x,y))
             _ -> failD 2 [Ds message4,Dd rng]
         Nothing -> let (tname,propMaybe) = root thclass rng
                    in ifM (allM (isProp propMaybe) (rng:doms))
                           (return (Chain(tname,map makeRel doms,rng)))
                           (do { bad <- filterM (\ x -> isProp propMaybe x >>= return . not) (rng:doms)
                               ; return (NotATheorem bad)})
     }

baseIsEquality (TyEx zs) vs =
   case unsafeUnwind zs of
     (us,([],t)) -> baseIsEquality t (us++vs)
     (us,(ps,t)) -> Nothing
baseIsEquality x vs =
   case equalPartsM x of
    Just(c,x,y) -> case c x y of
                   Equality _ _ -> Just(vs,x,y)
                   _ -> Nothing -- filter out TagNotEqual
    Nothing -> Nothing

-- When adding axioms, we need to assume the type being defined
-- is a proposition, since it hasn't been added to the list of
-- propositions yet, so we must tell isProp this. let the theorem
-- be a type like: dom1 -> dom2 -> rng,   where rng = (T x y z)

root thClass rng =
   case rootT rng [] of
     Nothing -> ("?",Nothing)
     Just(sx,lev,tname,kind,args) ->
              case thClass of
                (Just Axiom) -> (tname,Just tname)
                other        -> (tname,Nothing)

message4 =
 "\nIn a rewrite rule, the lhs must be a type-function call (like {plus x y}) or\n" ++
 "a type-constructor application (like (Even x)), otherwise it can't be\n" ++
 "used as a rewrite rule. This is not the case for:\n  "


sigmaToRule rclass (name,sigma) =
 do { x <- instanTy [] sigma        -- The instanTy, generalize sequence
    ; (_,K _ (Forall xs)) <- generalize x   -- removes Equality predicates
    ; (args,(conds,rho)) <- unwind xs
    ; let thclass = case rclass of
                      Nothing -> BackChain
                      (Just c) -> c
    ; info <- whatKind rclass rho
    ; case info of
        LeftToRight(vs,key,precond,lhs,rhs) ->
          do { commutes <- instanceOf args lhs rhs
             ; return[(key,RW name key (Rewrite commutes) (args++vs)
                             (precond++conds) (makeRel lhs) [(makeRel rhs)])] }

        Chain(key,doms,rng) ->
          let (_,bound,_) = varsOfTau rng
              (_,fr,_) = varsOfPred (doms ++ conds)
              eq (nm1,k1) (nm2,k2) = nm1==nm2
              free = deleteFirstsBy eq fr bound
              -- g (nm,k,q) = if any (eq (nm,k)) free then (nm,k,Ex) else (nm,k,All)
              g (nm,k,q) = (nm,k,All)
              args2 = map g args
              lhs = makeRel rng
              rhs = if (null free) then doms else []
              preCond = conds ++ (if (null free) then [] else doms)
              ans = [(key,RW name key thclass args2 preCond lhs rhs)]
          in return ans
        NotATheorem bad -> (warnM [Ds "\nIn the theorem '",Ds name, Ds "' the type:\n   " ,Dd rho
                              ,Ds "\nis neither a back-chaining nor a left-to-right rewrite rule."
                              ,Ds "\nbecause the following are not propositions:\n   ",Dl bad "\n   "
                              ,Ds "\nThus, no rule is added.\n"])
                        >> (return[])

    }

rhoArrowParts (Rtau z) = return(down [] z)
  where down xs (TyApp (TyApp (TyCon sx _ "(->)" _) x) y) = down (x:xs) y
        down xs z = (reverse xs,z)
rhoArrowParts r =
   failM 3 [Ds "\nThe type for a theorem cannot be a rankN type yet:\n", Dd r]

isProp:: Maybe String -> Tau -> TC Bool
isProp propMaybe t =
  case rootT t [] of
   Just(sx,lev,s,k,xs) -> case propMaybe of
                    (Just new) | s==new -> return True
                    other -> do { env <- tcEnv;
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
          do { (K _ sigma,mod,n,exp) <- lookupVar v
             ; case sigmaToRefinementRule nm sigma of
                Just rule -> return[("Equal",rule)]
                Nothing -> sigmaToRule Nothing (nm,sigma) }
        f (Global nm,Just term) =
          do { (sigma,_) <- infer term
             ; case sigmaToRefinementRule nm sigma of
                Just rule -> return[("Equal",rule)]
                Nothing -> sigmaToRule Nothing (nm,sigma) }
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
-- by enclosing decls. At top level, there are no enclosing decls
-- and the only constraints that get passed upwards are ones with
-- no variables (we hope). Here is where we try and solve them.

checkAndCatchGroundPred ds =
  do {((ds2,env),ground::[Pred]) <- extractAccum(checkBndGroup ds)
     ; let message = "Solving toplevel ground terms"
     ; (u,unsolved,_,_) <- solveConstraints (message,starR) env ground
     ; injectA " checkAndCatch " unsolved
     ; return(ds2,env)
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
     ; exts <- getSyntax
     ; (_,argsAsNames,(argEnv,_,_,_)) <- argsToEnv argBinds ([],loc,exts,[])
     ; (tau,monoKind,_) <- inferPT argEnv pt
     ; let g [] t = t
           g ((nm,k,q):ks) t = karr k (g ks t)
     ; (levs,polykind) <- generalize(g argsAsNames monoKind)
     ; let f (nm,k,_) = (nm,k)
           ans = case length args of
                  0 -> TySyn nm 0 [] [] tau
                  n -> TySyn nm n (map f argsAsNames) [] tau
     ; return([d],env{type_env = (nm,ans,polykind):(type_env env)})
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
     ; env <- (letExtend (bindingGroupNames "a data declaration that binds" ds) frag tcEnv)
     ; return(ds2,env)
     }
checkBndGroup ds =
  do { (frag,ds2) <- inferBndrForDecs "Top level" False ds
     ; env <- letExtend (bindingGroupNames "a top-level declaration that binds" ds) frag tcEnv
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

-- free variables in predicates at top level probably cannot
-- be solved. At Toplevel we expect predicates that are ground
-- terms, so if we get any with free vars, we just abstract over them.
-- So we need to split a [Pred] into ([Pred],[Pred]), those with
-- free (to be abstracted over) and those that are ground (to solve).

partByFree oblig = do { ps <- mapM free oblig; return(foldr acc ([],[],[]) ps)}
  where free p = do { (vs,_) <- get_tvs p; return(vs,p) }
        acc ([],p) (free,hasVars,ground) = (free,hasVars,p:ground)
        acc (vs,p) (free,hasVars,ground) = (vs++free,p:hasVars,ground)

wellTyped :: TcEnv -> Exp -> FIO (String,Exp,[String])
wellTyped env e = tcInFIO env
  (do { ((t::Rho,term),oblig) <- collectPred(inferExp e)
      ; truths <- getAssume
      ; (vs,passOn,solvePs) <- partByFree oblig
      -- ; warnM [Ds "Vars in Toplevel term: ",Dl vs ", " ]
      -- ; warnM [Ds "Obligations at top level are: ",Dd oblig]
      ; (oblig2,_,_) <- liftNf norm2PredL solvePs
      ; env <- tcEnv
      ; (u,oblig3,_,_) <- solveConstraints (show e,t) env oblig2
      ; (typ,_,_) <- liftNf norm2Rho t
      ; when (not(null oblig3) && not(arrowP typ))
             (failD 0 [Ds "Unresolved obligations:\n  ",Dl oblig3 "\n  "
                      , Ds " => ", Dd typ])
      ; (levels,polyk@(K level sig)) <- generalize(passOn++oblig3,typ)
      -- instantiate whatever levels are generalized over     
      ; let mkLevSub (v,TcLv(LvVar nm)) = do { x <- newLevel; return (LvVar nm,x)}
      ; sub2 <- mapM mkLevSub levels
      ; let sigma2 = sub2Sigma (sub2,[]) sig
      ; let kind x = do { k <- kindOfM x
                        ; (_,s) <- showThruDisplay [Dd x,Ds " :: ",Dd k]
                        ; return s}
      ; let subterms = (subtermsSigma sigma2 [])
      ; pairs <-  handleM 2  (mapM kind subterms) (\ _ -> return[])
      ; (_,typeString) <- showThruDisplay [Dd polyk,Ds "\n"]
      ; return(typeString,term,pairs)})


            
varTyped nm env = tcInFIO env
  (case getVar nm env of
    Nothing -> return Nothing
    Just(poly@(K levels sig),mod,cdlev,exp) ->
      do { -- instantiate whatever levels are generalized over     
           let mkLevSub nm = do { x <- newLevel; return (LvVar nm,x)}
         ; sub2 <- mapM mkLevSub levels
         ; let sigma2 = sub2Sigma (sub2,[]) sig
         ; let kind x = do { k <- kindOfM x; (_,s) <- showThruDisplay [Dd x,Ds " :: ",Dd k]; return s}
         ; pairs <- mapM kind (subtermsSigma sigma2 [])
         ; return(Just(poly,mod,cdlev,exp,pairs)) }
  )
    
    

arrowP (Rarrow _ _) = True
arrowP (Rtau (TyApp (TyApp (TyCon sx l "(->)" k) x) y)) = True
arrowP _ = False

arrowParts (TyApp (TyApp (TyCon sx _ "(->)" k) x) y) = Just(x,y)
arrowParts x = Nothing

tcInFIO :: TcEnv -> TC x -> FIO x
tcInFIO env e =
  do { (x,ns::[Pred]) <- unTc e env
     ; if null ns
          then return x
          else fail ("\nUnresolved NEED: "++show ns)}


-------------------------------------------------------------------
-- :norm typ     normalize type command

normString env s =
  do { map1 <- getTypeEnv
     ; parseT <- (parseType s)
     ; let (free,freeLevels) = getFree [] parseT
     ; (map2,vs,us) <- genericEnv free
     ; ty <- toTau (map1++map2,location env,syntaxExt env,[]) parseT
     ; (k::Tau,newTau) <- infer ty
     ; d0 <- readRef dispRef
     ; let (d1,cntxt) = displays d0 [Dd newTau]
     ; writeRef dispRef d1

     ; (refinement,ps) <- refine [] [(tauToPred newTau)] []
     ; warnM [Ds"\n   ",Dd newTau,Ds "\nNormalizes to:\n  ",Dl ps "\n  "
             ,Ds "\nRefinement:\n  ",Dl refinement "\n  "]
     ; return env
     }


-------------------------------------------------------------------
-- Used for the :narrow command
narrowString env count s =
  do { map1 <- getTypeEnv
     ; (n,parseT) <- (parseIntThenType count s)
     ; let (free,freeLevels) = getFree [] parseT
     ; outputString (show free)
     ; (map2,vs,us) <- genericEnv free
     ; ty <- toTau (map1++map2,location env,syntaxExt env,[]) parseT
     ; (k::Tau,newTau) <- infer ty
     ; d0 <- readRef dispRef
     ; let (d1,cntxt) = displays d0 [Dd newTau]
     ; writeRef dispRef d1
     ; (sols,(_,_,d1,ex)) <- narr cntxt (20,n,d1,False) [(TermP newTau,andR[],([],[]))] []
     ; if null sols && not ex
          then warnM [Ds "\nNo possible solutions\n"]
          else showSols us (newToOld ex sols)
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

parseAndKind :: TcEnv -> [Char] -> FIO (Kind,Tau,[String])
parseAndKind env s = tcInFIO env
    (
    do { map1 <- getTypeEnv
       ; s <- toTau (map1,location env,syntaxExt env,[]) (parsePT s)
       ; (tau::Tau,s2) <- infer s
       ; let kind x = do { k <- kindOfM x; (_,s) <- showThruDisplay [Dd x,Ds " :: ",Dd k]; return s}
       ; pairs <- mapM kind (subtermsTau tau [])
       ; return(MK tau,s2,pairs)
       -- ; return(MK (kindOf s2),s2)
       })


----------------------------------------------------------

elemsToString elems =
  do { d0 <- readRef dispRef
     ; let (d1,cntxt) = displays d0 elems
     ; writeRef dispRef d1
     ; return cntxt}



renderTau f t =
  do { d <- readRef dispRef
     ; let (d2,pt) = toPT d t
           string = render(f (ppPT pt))
     ; writeRef dispRef d2
     ; return string }

renderRho t =
  do { d <- readRef dispRef
     ; let (d2,pt) = rho2PT d t
           string = render(ppPT pt)
     ; writeRef dispRef d2
     ; return string }


ppProb d (TermP t) = (d2,ppPT x) where (d2,x) = toPT d t
ppProb d (EqP (x,y)) = (d2,ppPT z) where (d2,z) = toPT d (teq x y)
ppProb d (AndP ts) = (d2,text "And " <> PP.sep docs)
   where (d2,docs) = toL ppProb d ts

renderProb f t =
  do { d <- readRef dispRef
     ; let (d2,doc) = ppProb d t
           string = render(f doc)
     ; writeRef dispRef d2
     ; return string }


