-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Thu Jun 23 11:51:26 Pacific Daylight Time 2005
-- Omega Interpreter: version 1.1 (revision 1)

module Infer2 where

import Data.FiniteMap
import Monad(when,foldM)
import Monads
import Bind
import Syntax
import RankN
import List(partition,sort,sortBy,nub,union,unionBy,deleteFirstsBy,groupBy)
import Encoding2
import Auxillary(plist,plistf,Loc(..),report,foldrM,extend,extendL,backspace
                ,DispInfo(..),Display(..),initDI,newDI,dispL,disp2,disp3,disp4
                ,DispElem(..),displays,mergeDisp,ifM,anyM,allM,ifM)
import LangEval(vals,env0,Prefix(..),elaborate)
import ParserDef(pCommand,parseString,Command(..),getExp)
import IO (openFile,hClose,IOMode(..),hPutStr)
import Char(isAlpha)
import ParserDef(parse2, program)
import IOExts(unsafePerformIO)
import SCC(topSortR)

pstr :: String -> TC ()
pstr = outputString

appendFM map key element = addToFM_C add map key [element]
  where add old new = old ++ new
  
appendFM2 map [] = map
appendFM2 map ((key,element):xs) = addToFM_C add (appendFM2 map xs) key element
  where add old new = old ++ new  

appendFMmany map []  = map
appendFMmany map ((k,e):xs) = appendFMmany (appendFM map k e) xs 

---------------------------------------------------------------------------
-- Set up the TC monad

localRename = False

type TC a = Mtc TcEnv Pred a

inEnv :: TcEnv -> TC c -> TC c
inEnv env (Tc f) = Tc(\ x -> f env)
tcEnv :: TC TcEnv
tcEnv = (Tc (\ env -> return(env,[])))

instance TyCh (Mtc TcEnv Pred) where
   envTvs = do { (vs,triples) <- getVarsFromEnv; return vs}
   handleM = handleTC
   assume preds unifier m = 
        do { env <- tcEnv
           ; let env2 = env { bindings = composeMGU unifier (bindings env) 
                            , assumptions = preds ++ (assumptions env) }
           ; inEnv env2 m
           }
   getBindings = do { env <- tcEnv; return(bindings env) }
   getDisplay = (Tc ( \ env -> return(displayInfo env,[])))
   lookupTyFun s = 
     do { table <- getTyFuns; return(lookup s table) }
   solve = solveConstraints

getAssume = do { env <- tcEnv; return(assumptions env) }
getMatchingRules s = do { env <- tcEnv; return(getRules s env)}
getRefutation s = 
   do { env <- tcEnv
      ; case lookupFM (refutations env) s of
         Nothing -> return(\ x -> return ())
         Just ts -> return(ts)}

instance TracksLoc (Mtc TcEnv Pred) where
  position = do { l <- getLoc; return l}
  failN dis loc n s = Tc h
    where h env = FIO(return(Fail dis loc n s))

-------------------------------------------------------------------------
-- The type checking environment TcEnv and its auxillary data types

-- type ToEnv = [(String,Tau,PolyKind)] -- In RankN.hs
data Frag = Frag [(Var,(Sigma,Level,Exp))] [TcTv] ToEnv 
                 [Pred] [(String,Rule)]

interesting (Frag env skols _ eqn rules) = not(null eqn)

nullFrag = Frag [] [] [] [] []

type Level = Int
type Refutation = Tau -> TC ()

-- The type of the internal environment of the Type Checking Monad
data TcEnv 
  = TcEnv { var_env :: FiniteMap Var (Sigma,Level,Exp) -- Term Vars
          , type_env :: [(String,Tau,PolyKind)] -- Type Vars
          , generics :: [(Var,Sigma)]    -- Lambda Bound Names
          , verbose :: Bool              -- Interactive Type Checking on?
          , level :: Int                 -- code level, counts brackets
          , location :: Loc              -- position in file
          , bindings :: MGU              -- equality bindings
          , assumptions :: [Pred]        -- assumptions
          , rules :: FiniteMap String [Rule] -- Proposition simplifying rules
          , refutations :: FiniteMap String Refutation 
          , runtime_env :: Ev            -- current value bindings
          , imports :: [(String,TcEnv)]  -- already imported Modules
          , displayInfo :: DispInfo      -- display info
          , tyfuns :: [(String,[Tau]-> TC Tau)] 
          }

tcEnvEmpty = TcEnv emptyFM toEnvX [] False 0 Z [] [] emptyFM emptyFM env0 [] initDI []


----------------------------------------------------------
-- A class of data structures that are binding instances

class TypableBinder term where
  checkBndr :: Bool -> term -> Sigma -> TC(Frag,term)
  inferBndr :: Bool -> term -> TC(Sigma,Frag,term)

----------------------------------------------------------------
-- simple operations on Frag and TcEnv

-- One can perform substitution and zonking on Frags

instance TypeLike (Mtc TcEnv Pred) Frag where
  sub env (Frag xs ys zs eqs rs) =
     do { xs' <- mapM f xs;
        ; eqs2 <- sub env eqs
        ; zs' <- mapM g zs
        ; rs2 <- mapM (sub env) rs
        ; return(Frag xs' ys zs' eqs2 rs2)}
    where f (v,(s,lev,exp)) = do { s2 <- sub env s; return(v,(s2,lev,exp))}
          g (str,tau,kind) =
            do { t2 <- sub env tau; k2 <- sub env kind; return(str,t2,k2)}
  zonk (Frag xs ys zs eqs rs) =
    do { xs2 <- mapM f1 xs; eqs2 <- mapM zonk eqs
       ; rs2 <- mapM zonk rs; return(Frag xs2 ys zs eqs2 rs2)}
   where f1 (x,(y,z,w)) = do { y' <- zonk y; return(x,(y',z,w))}
  get_tvs f = error "No way to get the type vars from a Frag"
  nf x = error "Can't put frags in normal form"
  
infixr +++
(Frag xs ys zs eqs rs1) +++ (Frag as bs cs eqs2 rs2) = 
  Frag (xs++as) (ys++bs) (zs++cs) (eqs++eqs2) (rs1++rs2) 

getTyFuns :: TC [(String,[Tau]-> TC Tau)]
getTyFuns = Tc (\ env -> return (tyfuns env,[]))

addPred :: [Pred] -> Frag -> TC Frag
addPred truths (Frag xs ys zs eqs rs) = return(Frag xs ys zs (truths++eqs) rs)

getTCEnv :: TC (FiniteMap Var (Sigma,Level,Exp))
getTCEnv = Tc (\ env -> return (var_env env,[]))

getGenerics :: TC [(Var,Sigma)]
getGenerics = Tc (\ env -> return (generics env,[]))

getLevel :: TC Int
getLevel = Tc (\ env -> return (level env,[]))

getLoc :: TC Loc
getLoc = Tc (\ env -> return (location env,[]))

getTypeEnv :: TC [(String,Tau,PolyKind)]
getTypeEnv = Tc (\ env -> return (type_env env,[]))

getkind :: Monad m => [Char] -> TcEnv -> m (PolyKind,Tau)
getkind x env = f (type_env env)
   where f [] = fail ("Unknown type: "++x)
         f ((y,t,k):xs) = if x==y then return(k,t) else f xs

showAllVals n env = mapM f (take n (fmToList(var_env env)))
  where f (nm,(sigma,level,exp)) = outputString (show nm ++ " : " ++alpha [] sigma)

showSomeVals p env = mapM f (filter p (fmToList(var_env env)))
  where f (nm,(sigma,level,exp)) = outputString (show nm ++ " : " ++alpha [] sigma)


mknoisy env = env { verbose = True }
mksilent env = env { verbose = False }

collectPred :: TC a -> TC (a,[Pred])
collectPred = extractAccum

setDisplay :: DispInfo -> Mtc TcEnv a b -> Mtc TcEnv a b
setDisplay d (Tc m) = Tc(\env -> m (env {displayInfo = d}));

--------------------------------------------------
-- Manipulating the environment part of the monad

letExtend :: [Pred] -> MGU -> Frag -> TC a -> TC a
letExtend preds unifier (Frag pairs rigid tenv eqs rs) (Tc m) = Tc (\env -> m (extend env))
  where extend env = env { var_env = addListToFM (var_env env) pairs
                         , type_env = tenv ++ (type_env env)
                         , bindings = composeMGU unifier (bindings env)
                         , assumptions = preds ++ (assumptions env)
                         , rules = appendFMmany (rules env) rs}

lambdaExtend :: [Pred] -> MGU -> Frag -> TC a -> TC a
lambdaExtend preds unifier (Frag pairs rigid tenv eqs rs) (Tc m) = Tc (\env -> m (extend env))
  where g (x,(rho,lev,exp)) = (x,rho)
        extend env = env { var_env = addListToFM (var_env env) pairs
                         , generics = (generics env) ++ map g pairs
                         , bindings = composeMGU unifier (bindings env)
                         , assumptions = preds ++ (assumptions env)
                         , rules = appendFMmany (rules env) rs
                         }

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

addFrag (Frag pairs rigid tenv eqs rs) env = extend env
  where extend env = env { var_env = addListToFM (var_env env) pairs
                         , type_env = tenv ++ (type_env env)
                         , bindings = composeMGU unifier (bindings env)
                         , rules = appendFMmany (rules env) rs}
        (Left unifier) = mgu (map f eqs)
        f (Equality x y) = (x,y)
        
addLetFrag (Frag pairs rigid tenv eqs rs) env =
    env { var_env = addListToFM (var_env env) pairs
        , bindings = composeMGU unifier (bindings env)
        , rules = appendFMmany (rules env) rs}
 where (Left unifier) = mgu (map f eqs)
       f (Equality x y) = (x,y)

levelInc :: TC a -> TC a
levelInc (Tc m) = Tc (\env -> m (env {level = (level env) + 1}))

levelDec :: TC a -> TC a
levelDec (Tc m) = Tc (\env -> m (env {level = (level env) - 1}))

newLoc :: Loc -> TC a -> TC a
newLoc loc (Tc m) = Tc (\env -> m (env {location = loc}))

lookupVar :: Var -> TC (Sigma,Level,Exp)    -- May fail
lookupVar n = do { env <- getTCEnv
                 ; case lookupFM env n of
                     Just ty -> return ty
                     Nothing -> failD 2 [Ds "Not in scope: ", Dd n]}

getVar :: Var -> TcEnv -> Maybe(Sigma,Level,Exp)
getVar nm env = lookupFM (var_env env) nm

getRules :: String -> TcEnv -> [Rule]
getRules nm env =
  case lookupFM (rules env) nm of
    Nothing -> []
    Just ts -> ts

-----------------------------------------------------------------
-- Types in syntax are stored as PT, we need to translate them
-- into Sigma types, and check that their well formed with Kind *
-- PT types stored in Data Decs are handled differently because they
-- may have kinds other than *, and they are not always generalized.
-- We return a Sigma type, and a Fresh Rho type, and a Display mapping
-- mapping the Unique integers in the fresh Rho to the Strings in the PT

checkPT :: PT -> TC(Sigma,([(Integer,String)],Rho,[Pred]))
checkPT pt = 
  do { tenv <- getTypeEnv
     ; (free,pt2) <- splitPT tenv pt  -- Make sure its an explcit Forallx form
     ; freeEnv <- mapM genFresh free  -- Make temp Types for translating free typevars
     ; (s@(Forall xs),snMap) <- toSigma (freeEnv ++ tenv) pt2 -- translate
     ; check s (Star 0)                                       -- check the translation has kind *0
     ; let (names,(eqns,rho)) = unsafeUnwind xs               -- unwind to make a fresh Rho instance
     ; (nameMap,stringMap) <- rigid snMap names []            -- build the mappings
     ; rho2 <- sub (nameMap,[],[]) rho            -- make fresh Rho
     ; eqn2 <- sub (nameMap,[],[]) eqns           -- and fresh equations
     ; return (s,(stringMap,rho2,eqn2))}
 where  genFresh nm = 
          do { kind <- newKind star1; var <- newFlexiTyVar kind
             ; return(nm,TcTv var,poly kind)}            
        unique (Tv n f k) = n
	rigid ((s,nm):xs) ((nm2,k,q):ys) subst = 
	    do { k2 <- sub (subst,[],[]) k    -- in explicit foralls, earlier may bind
	       ; v <- newRigidTyVar q Z s k2  -- later, so we need to apply subst to k
	       ; (subst2,ms) <- rigid xs ys ((nm,TcTv v):subst)
	       ; return(subst2,(unique v,"_"++s):ms)}
        rigid _ _ subst = return(subst,[])
                  
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

--------------------------------------------------------------------
-- Literals are Typable

instance Typable (Mtc TcEnv Pred) Lit Rho where
  tc x@(Int n) expect = zap x (Rtau intT) expect
  tc x@(Char c) expect = zap x (Rtau charT) expect
  tc x@(Unit) expect = zap x (Rtau unitT) expect
  tc x@(ChrSeq s) expect = zap x (Rtau chrSeqT) expect
  tc x@(Symbol n) expect = zap x (Rtau symbolT) expect
  tc x@(Float n) expect = zap x (Rtau floatT) expect
  tc x@(Tag s) expect = zap x (Rtau (ttag s)) expect

--------------------------------------------------------------------
-- Functions to report reasonably readable  errors

notfun e fun_ty dis s =
   failDd 2 dis [Ds "\nIn the expression: "
                ,Dd e
                ,Ds "\nthe function has a non-functional type: "
                ,Dd fun_ty]

badarg e arg_ty dis s = 
 do { z <- zonk arg_ty
    ; failDd 2 dis 
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
     ; failDd 2 info1
         [Ds "\nIn the expression: "
         ,Dn e
         ,Ds "the result type: "
         ,Dn rt
         ,Ds "was not what was expected: "
         ,Dn ex
         ,Ds s]}

morePoly::(Exhibit DispInfo a,Exhibit DispInfo b,Exhibit DispInfo c,Subsumption m b(Expected c),TypeLike m b,TypeLike m c)
          => a -> b -> Expected c -> m ()
morePoly exp sigma expect =
   handleM 2 (morepoly sigma expect) (resulterr exp sigma expect)


--------------------------------------------------------------------
-- This instance is useful for a first class pattern decl like:
-- pattern LHS = RHS
-- pattern If x y z = Case x [(True,y),(False z)]
-- where we need to check that the pattern on the RHS is well formed
-- when using the variables defined on the LHS.

instance Typable (Mtc TcEnv Pred) Pat Rho where
  tc (Plit l) expect = do { l2 <- tc l expect; return(Plit l2) }
  tc (Pvar v) expect =
     do { (sigma,n,Var u) <- lookupVar v
        ; morePoly (Pvar v) sigma expect
        ; return(Pvar u)}
  tc (z@(Pexists p)) _ = 
     failD 1 [Ds "No exist patterns in pattern decls: ",Dd z] 
  tc pat@(Psum inj x) (Check (Rsum t1 t2)) = -- t1 or t2 or both are non-trivial Sigmas
     do { (sig::Sigma,e) <- infer x
        ; case inj of { L -> morepoly t1 sig; R -> morepoly t2 sig }
        ; return (Psum inj e) }
  tc (Psum inj x) expect =
     do { (a,b) <- expecting "Sum" tsum expect
        ; e <- check x (case inj of { L -> a; R -> b })
        ; return(Psum inj e) }

  tc (Pprod x y) (Check (Rpair t1 t2)) = -- t1 or t2 or both are non-trivial Sigmas
     do { (s1::Sigma,e1) <- infer x
        ; (s2::Sigma,e2) <- infer y
        ; morepoly t1 s1
        ; morepoly t2 s2
        ; return (Pprod e1 e2) }
  tc (Pprod x y) expect =
     do { (a,b) <- expecting "Pair" tpair expect
        ; e1 <- check x a
        ; e2 <- check y b
        ; return (Pprod e1 e2) }

  tc p@(Pcon c ps) expect =
     do { (sigma,n,exp) <- lookupVar c
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
  checkBndr rename var t =
     do { level <- getLevel
        ; v <- alphaN rename var
        ; return(Frag [(var,(t,level,Var v))] [] [] [] [],v) }
  inferBndr rename var =
     do { sigma <- newSigma star;
        ; level <- getLevel
        ; v <- alphaN rename var
        ; return(sigma,Frag [(var,(sigma,level,Var v))] [] [] [] [],v) }


constrRange [] t = return t
constrRange (p:ps) t = do { (dom,rng) <- unifyFun t; constrRange ps rng }
--constrRange _ t = fail "Range of a constructor must me a Tau type"

instance TypableBinder Pat where
  checkBndr rename p t = ch p where
     ch (Plit x) = check x t >> return(nullFrag,p)
     ch (Pvar v) = do { (frag,u) <- checkBndr rename v t; return(frag,Pvar u)}
     ch (Pprod x y) =
       do { --outputString ("Before sigmaPair" ++ show t);
            t2 <- zonk t
          ; ((t1,t2),truths) <- collectPred (sigmaPair t2)
          ; a1 <- zonk t1; a2 <- zonk t2
          --; outputString ("After sigmaPair" ++ show a1++ " | "++show a2)
          ; (frag1@(Frag vs _ _ eqs rs),p1) <- checkBndr rename x t1
          -- Facts generated in the first part of a tuple can be used to check the second
          ; (preds,unifier) <- handleM 3 (mguM eqs) (mErr 1 [] eqs x t1)
          ; (frag2,p2) <- factExtend preds unifier (checkBndr rename y t2)
          ; tZ <- zonk t
          ; frag3 <- addPred truths (frag1+++frag2)
          ; return(frag3,Pprod p1 p2)}
     ch (Psum inj p) =
       do { ((t1,t2),truths) <- collectPred (sigmaSum t)
          ; (frag1,p1) <- checkBndr rename p (case inj of {L -> t1; R -> t2})
          ; frag2 <- addPred truths frag1
          ; return(frag2,Psum inj p1)}
     ch (z@(Pexists p)) =
       case t of
        Forall (Nil([],Rtau(TyEx zs))) ->
          do { loc <- getLoc
             ; (rigid,assump,tau) <- instanExPat loc (show p) zs
             ; (frag,p2) <- checkBndr rename p (Forall(Nil([],Rtau tau)))
             ; return(frag+++(Frag [] rigid [] assump []),Pexists p2)
             }
        _ -> failD 1 
               [Ds "Exists patterns cannot have their type inferred:\n  "
               ,Dd z
               ,Ds " Use a prototype signature."]
     ch (Paspat v p) =
       do { (frag1,p1) <- checkBndr rename p t
          ; (frag2,u) <- checkBndr rename v t
          ; return(frag1+++frag2,Paspat u p1) }
     ch Pwild = return(nullFrag,Pwild)
     ch (Pcon c ps) =
       do { (sigma,n,exp) <- lookupVar c
          --; pstr ("In checkBndr t ="++show t++" sigma = "++show sigma)
          ; loc <- getLoc
          ; current <- getBindings
          --; outputString ("\n1 %% "++show c++" current = "++ show current++show sigma)
          ; (rigid,assump,rho) <- instanPatConstr Ex loc (show p) sigma
          ; range <- constrRange ps rho
          --; pstr ("range = "++show range++", t = "++show t++
          --        ", assump = "++show assump++", rho = "++show rho)
          ; (_,truths) <- collectPred (morepoly t range)
          ; ass <- zonk assump -- After the morepoly check we need to zonk
          ; r1 <- zonk rho
          ; t1 <- zonk t
          --; outputString ("2 %% "++show c++" assump = "++show assump++" ass = "++show ass)
          --; outputString ("3 %% "++show ass++show r1++" should have type "++show t)
          ; (frag,ps',result) <- checkBndrs rename ps r1
          ; frag3 <- addPred truths (frag+++(Frag [] rigid [] ass []))
          ; return(frag3,Pcon c ps')}
     ch (Pann p ty) =
       do { (sigma,_) <- checkPT ty
          ; (_,truths) <- collectPred (morepoly t sigma)
          ; (frag,p') <- checkBndr rename p t
          ; frag2 <- addPred truths frag
          ; return(frag2,p') }

  inferBndr rename p = inf p where
    inf (Plit x) = do {(t,l) <- infer x; return(t,nullFrag,Plit l)}
    inf (Pvar v) = do {(t,frag,u) <- inferBndr rename v; return(t,frag,Pvar u)}
    inf (Pprod x y) =
       do { (t1,frag1,p1) <- inferBndr rename x
          ; (t2,frag2,p2) <- inferBndr rename y
          ; let assump = []
          ; return(Forall (Nil (assump,pair t1 t2)),frag1+++frag2,Pprod p1 p2)}
    inf (Psum inj p) =
       do { (t,frag1,p1) <- inferBndr rename p
          ; s <- newSigma star
          ; let sumtyp = (case inj of {L -> rsum t s
                                      ;R -> rsum s t})
          ; let assump = []
          ; return(Forall (Nil (assump,sumtyp)),frag1,Psum inj p1)}
    inf (Paspat v p) =
       do { (t,frag1,p1) <- inferBndr rename p
          ; (frag2,u) <- checkBndr rename v t
          ; return(t,frag1+++frag2,Paspat u p1) }
    inf Pwild = do { t <- newSigma star; return(t,nullFrag,Pwild) }
    inf (Pcon c ps) =
       do { (sigma,n,exp) <- lookupVar c
          ; loc <- getLoc
          ; (rigid,assump,rho) <- instanPatConstr Ex loc (show p) sigma
          ; (frag,ps',result) <- checkBndrs rename ps rho
          ; let assump2 = []
          ; return(Forall (Nil (assump2,result)),frag+++(Frag [] rigid [] assump []),Pcon c ps')}
    inf pat@(Pann p ty) =
       do { (sigma,_) <- checkPT ty
          ; (frag,p') <- checkBndr rename p sigma
          ; return(sigma,frag,Pann p' ty)}
    inf (z@(Pexists p)) = 
      failD 1 [Ds "Exists pattern cannot be inferred: ",Dd z]
-----------------------------------------------------------------------

inferBndrs :: Bool -> [Pat] -> TC([Sigma],Frag,[Pat])
inferBndrs rename ps =
    do { ws <- mapM (inferBndr rename) ps; return(foldr acc ([],nullFrag,[]) ws)}
  where acc (r,frag1,p) (rs,frag2,ps) = (r:rs,frag1+++frag2,p:ps)


checkBndrs :: Bool -> [Pat] -> Rho -> TC(Frag,[Pat],Rho)
checkBndrs rename ps result_ty = checkBs rename nullFrag ps result_ty

checkBs rename f0 [] result_ty = return(f0,[],result_ty)
checkBs rename f0 (p:ps) rho =
  do { (dom,rng) <- unifyFun rho
     ; (frag1@(Frag vs _ _ eqs rs),p1) <- handleM 2 (checkBndr rename p dom) (pErr p ps dom)
     -- Facts generated in earlier patterns can be used to check later patterns
     ; let binds (Frag vs _ _ _ _) = vs
     ; (preds,unifier) <- handleM 3 (mguM eqs) (mErr 2 (binds f0) eqs p dom)
     ; (frag2,ps1,result_ty) <- factExtend preds unifier (checkBs rename (frag1+++f0) ps rng)
     ; return(frag2,p1:ps1,result_ty) }

type Binding = (Var,(Sigma,Level,Exp))

mErr (n::Int) (vs::[Binding]) eqs p dom d1 mess =
  do {truths <- getBindings
     ; failDd 2 d1
        [Ds "\nWhile checking that the pattern "
        ,Dd p, Ds " : ", Dd dom
        ,Ds "\nwe found this inconsistent with the current bindings:\n   "
        ,Df dbinds vs
        ,Ds "\nand equations:\n   "
        ,Df deqs truths
        ,Ds "\nBecause it requires solving: "
        ,Dl eqs ", "
        ,Ds "\nThis probably means this clause is unreachable code. "
        ,Ds (show n)]}
        
deqs d xs = dispL f d xs ", "
  where f d (a,b) = (d1,x++"="++y) where (d1,x,y) = disp2 d (a,b)
dbinds d xs = dispL f d xs ", "
  where f d (a,(b,_,_)) = (d1,x++":"++y) where (d1,x,y) = disp2 d (a,b)  

pErr p moreps dom d1 mess = 
  failDd 2 d2 [Ds "While checking that the pattern: "
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

checkDataDecs :: Strata -> [Dec] -> TC (Sigma,Frag,[Dec])
checkDataDecs strata ds =
  do { (tmap,cmap) <- doManyData strata ds 
     ; let propList = foldr isProp [] tmap -- Get list of props from mutRecDatas
           isProp (True,name,_,_) ps = name:ps
           isProp (False,name,_,_) ps = ps
     ; tmap2 <- mapM genTyCon tmap
     ; let f (nm,tau,polykind) = (nm,tau)
     ; cmap2 <- genConstrFunFrag (map f tmap2) (map snd cmap)
     ; let liftToTypeEnv (Global s,(sig,n,exp)) = (s,TyCon s (K sig),K sig)
           makeRule (True,(Global c,(sigma,_,_))) = 
              do { ((preds,rho),lhsRho) <- splitIntoPredsRho sigma
                 ; x <- case lhsRho of
                     Rtau lhsTau -> 
                            do { (doms,rng) <- splitRho lhsRho
                               ; sigmaToRule propList rng c preds rho }
                     _ -> failD 0 [Ds "Rule has Rank N type ",Dd sigma]
                 ; return [x]}
           makeRule (False,(Global c,(sigma,_,_))) = return []
           (types,values) = 
             if strata == typeStrata
                then (tmap2,cmap2)
                else (map liftToTypeEnv cmap2 ++ tmap2,[])
     ; rules <- mapM makeRule cmap
     ; return(simpleSigma unitT,Frag values [] types [] (concat rules),ds)
     }

-- translate a [Pred] from a Maybe[Pred]           
toPred env Nothing = return[]
toPred env (Just xs) = toEqs env xs
 
doManyData strata ds = 
  do { envMap <- getTypeEnv
     ; let proj (x,y,z) = (x,y)
     ; info <- mapM (dataBinds strata envMap) ds
     ; let acc (t,c) (ts,cs) = (t:ts,c++cs)
           (tMap,constrBinds) = foldr acc ([],[]) info
           project (isprop,name,sig,tau) = (name,sig,tau)
     ; let g (loc,isprop,name,allExParams,env2,eqs,body) = 
             do { let env3 = env2 ++ (map project tMap)
                ; eqs2 <- toPred env3 eqs
                ; body2 <- toRho env3 body
                ; let typ = Forall (windup allExParams (eqs2,body2))
                ; newLoc loc $ hasKind name typ (MK (Star strata))
                ; typ2 <- zonk typ
                --; warn [Ds ("\n"++name++" :: "),Dd typ2]
                ; return(isprop,(Global name,(typ,0::Level,Var(Global name))))
                }
     ; cMap <- mapM g constrBinds
     ; return (tMap,cMap)
     }
    
-- compute typings and kindings from a Dec, they'll be checked later in "doManyData"

dataBinds:: Strata -> (ToEnv) -> Dec -> TC((Bool,String,Tau,PolyKind),[ConType])
dataBinds strata currentEnv (Data loc isprop _ (t@(Global tname)) sig xs cs derivs) = 
  do { let (allArgs,eqs,hint) = sigToForallParts strata sig
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
     --; outputString ("AllEnv = " ++ show allEnv++"\ntkindbody = "++show tkindbody)
     ; rho <- toRho allEnv tkindbody
     ; tkind <- return (K(Forall (windup allParams ([],rho))))
     ; return((isprop,tname,TyCon tname tkind,tkind),cTypes) }


type ConType = (Loc,Bool,String,ForAllArgs,ToEnv, Maybe[PPred],PT)


conType :: Bool -> Strata -> ForAllArgs -> (ToEnv) -> PT -> Constr -> TC ConType
conType isprop strata allParams allEnv rng (cc@(Constr loc exs c@(Global cname) ts eqs)) = 
    do {(_,exParams,allExEnv) <- argsToEnv (map f exs) allEnv
       ; return(loc,isprop,cname,allParams ++ exParams,allExEnv,eqs,cbody) }
  where f (Global s,k) = (s,k,Ex)
        cbody = foldr arr rng ts
        arr = (if strata == typeStrata then Rarrow' else Karrow')

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
  walk [] (Just (Star' n)) 
        | n == strata = return ([],Star' strata) -- explicit (T a b):: *
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
    if samePT d1 d2
       then do { (xs,rng) <- walk vs (Just r)
               ; return((v,d1,All):xs,rng) 
               }
       else failD 2 [Ds "data Dec has explicit signature and explicit kindings on arguments, "
                    ,Ds "but they don't match. "
                    ,Dd d1, Ds " != ",Dd d2]
  walk (v:vs) (Just t) = failD 2 [Ds "Expecting kind arrow like (a ~> b), found: ",Dd t]


genConstrFunFrag tyConSub xs = mapM f xs where
  f (nm,(sig,lev,exp)) =
    do { -- Replace TyCon's which have stale (i.e. mono) PolyKind fields
         sig1 <- sub ([],[],tyConSub) sig
       ; sig3 <- generalize sig1  -- Now generalize
       ; return(nm,(sig3,lev,exp))}

genTyCon :: (Bool,String,Tau,PolyKind) -> TC (String,Tau,PolyKind)
genTyCon (isprop,nm,TyCon _ _,K k) =
  do { k2 <- generalize k
     ; return(nm,TyCon nm (K k2),K k2) }

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


instance TypableBinder [Dec] where
  inferBndr renm [] = return(simpleSigma unitT,nullFrag,[])
  -- inferBndr renm ds | all isData ds= checkDataDecs typeStrata(useTypeSig ds)
  -- inferBndr renm ds | all isKind ds= checkDataDecs kindStrata(useTypeSig ds)
  inferBndr renm ds | all isValFunPat ds =
    do { let decs = useTypeSig ds
       ; (frag@(Frag xs _ _ _ _),triples) <- getDecTyp renm decs -- Step 1
       --; (mapM_ displayFragElem xs)
       --; outputString("\nThe Triples are\n "++show triples)
       ; ds2 <- mapM (checkDec frag) triples -- Step 2
       ; frag2@(Frag xs zs tenv eqs rs) <- genFrag frag
       --; when (not renm) (mapM_ displayFragElem xs)
       ; return(simpleSigma unitT,frag2,ds2)
       }
  inferBndr rename ds = failD 2 [Ds "\nMixup in Decs\n", Ds (show ds)]
  checkBndr rename ds = error "Can't checkBndr a [Dec]"

-- Step 1. Compute just the "frag" for the decls. Don't do their bodies yet.

getDecTyp :: Bool -> [Dec] -> TC (Frag,[([(Integer,String)],Rho,Dec,[Pred])])
getDecTyp rename [] = return(nullFrag,[])
getDecTyp rename (d:ds) =
  do { (disp,frag1,rho,d,eqns) <- getOneDec rename d
     ; (frag2,triples) <- getDecTyp rename ds
     ; return(frag1 +++ frag2,(disp,rho,d,eqns):triples) }


getOneDec rename (Val loc (Pann pat pt) body ds) = newLoc loc $
  do { (sigma,(d1,rho,assump)) <- checkPT pt    -- use the hint to get rho and display
     ; (frag,pat2) <- checkBndr rename pat sigma
     ; frag2 <- addTheorem (show pat) frag sigma
     ; return(d1,frag2,rho,Val loc pat2 body ds,assump)}
getOneDec rename (Val loc pat body ds) = newLoc loc $
  do { (sigma,frag,pat2) <- inferBndr rename pat
     ; (rigid,assump,rho) <- rigidTy Ex loc (show pat) sigma
     ; return([],frag,rho,Val loc pat2 body ds,assump)}
getOneDec rename (Fun loc nm Nothing ms) = newLoc loc $
  do { sigma <- newSigma star
     ; (frag,nm2) <- checkBndr rename nm sigma
     ; (rigid,assump,rho) <- rigidTy Ex loc (show nm) sigma
     ; r1 <- zonk rho
     ; return([],frag,rho,Fun loc nm2 Nothing ms,assump)}
getOneDec rename (Fun loc (nm@(Global fname)) (Just pt) ms) = newLoc loc $
  do { (sigma,(d1,rho,assump)) <- checkPT pt -- use the hint to get rho and display
     ; (frag,nm2) <- setDisplay (newDI d1) (checkBndr rename nm sigma)
     ; r1 <- zonk rho
     ; frag2 <- addTheorem fname frag sigma
     ; return(d1,frag2,r1,Fun loc nm2 (Just pt) ms,assump)}
getOneDec rename (Pat loc nm vs p) = newLoc loc $
  do { (sigma,frag,nm2) <- inferBndr rename nm
     ; (rigid,assump,rho) <- rigidTy Ex loc (show nm) sigma
     ; return([],frag,rho,Pat loc nm2 vs p,assump)}
getOneDec rename (Reject s ds) = return ([],nullFrag,Rtau unitT,Reject s ds,[])
getOneDec rename (Prim l nm t) =
  do { (sigma,frag,_) <- inferBndr rename (Pann (Pvar nm) t)
     ; return([],frag,error "Shouldn't Check Prim type",Prim l nm t,[]) }
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

checkDec frag (d1,rho,Val loc pat body ds,eqns) = newLoc loc $
  do { (_,frag2,ds2) <- inferBndr localRename ds
     ; (preds,unifier) <- fragMGU ("Checking where clause of "++show pat) frag2
     ; frag3 <- addPred eqns frag 
     ; ((assump,body2),oblig) <- 
           collectPred
           (underLetGetPred ("CheckDec "++show pat) frag3
           (lambdaExtend preds unifier frag2 
           (setDisplay (newDI d1) (check body rho))))
     ; truths <- getAssume
     ; oblig2 <- solveConstraints (assump++truths) oblig
     ; when (not (null oblig2)) 
            (failD 3 [Ds "\nWhile type checking: ", Dd pat
                     ,Ds "\nUnder the truths: "
                     ,Dl (assump++truths) ", "
                     ,Ds "\nWe tried to solve: "
                     ,Dl oblig ","
                     ,Ds "\nBut we were left with: "
                     ,Dl oblig2 ", "])
     ; return(Val loc pat body2 ds2) }
checkDec frag (d1,rho,Fun loc nm hint ms,eqns) = newLoc loc $
  do { frag3 <- addPred eqns frag
     ; let hasRho m = check m rho
    ; ((assump,ms2),oblig) <- 
           collectPred 
           (underLamGetPred frag3 ("CheckDec "++show nm) 
           (setDisplay (newDI d1) (mapM hasRho ms)))
     ; truths <- getAssume
     --; warn [Ds "\nGetting ready to solve for ",Ds (show nm),Ds "\n"]
     ; oblig2 <- solveConstraints (assump++truths) oblig
     ; when (not (null oblig2)) 
                 (failD 3
                   [Ds ("\nWhile type checking: "++show nm)
                   ,Ds "\nUnder the truths: "
                   ,Dl (assump++truths) ", "
                   ,Ds "\nWe tried to solve: "
                   ,Dl oblig ", "
                   ,Ds "\nBut we were left with: "
                   ,Dl oblig2 ", "])
     ; return(Fun loc nm hint ms2) }
checkDec frag (d1,rho,Pat loc nm vs p,eqns) = newLoc loc $
  do { frag3 <- addPred eqns frag 
     ; (preds,unifier) <- fragMGU ("Checking "++show nm) frag3
     ; (Forall (Nil (assump,ty)),(Frag xs tvs tenv eqs rs),p2)
               <- lambdaExtend preds unifier frag3 (inferBndr False p)
     ; argtys <- compareL vs xs
     ; morepoly (foldr arrow ty argtys) rho
     ; return(Pat loc nm vs p2)
     }
     
checkDec frag (d1,rho,Reject s ds,eqns) =
  handleM 7 (do { (_,frag2,ds2) <- inferBndr localRename ds
                ; error ("\nReject test: "++s++" did not fail.")}) errF
 where errF dis _= do { outputString ("\n*** negative test '"++ s ++ 
                                  "' fails as expected\n")
                  ; return (TypeSig Z (Global "##test") tunit')}
checkDec frag (d1,_,Prim loc nm t,eqns) = newLoc loc $ return(Prim loc nm t)
checkDec frag d = failD 2 [Ds "Illegal dec in value binding group: ", Ds (show d)]

----------------
-- Helper functions for typing [Dec]

-- Generalize a Frag after type inference

genFrag (Frag xs ys tenv eqs rs ) = 
     do { zs <- mapM gen xs; return(Frag zs ys tenv eqs rs )}
  where gen (var,(sigma@(Forall (Nil b)),level,exp)) =
            do { s1 <- zonk sigma
               ; s2 <- generalize b; return (var,(s2,level,exp))}
        gen (var,(sigma,level,exp)) =
            do { s2 <- zonk sigma; return(var,(s2,level,exp)) }


-- Compare that all the vars in a pattern Dec are used

compareL :: TyCh m => [Var] -> [(Var,(ty,Level,exp))] -> m [ty]
compareL xs fs =
    do { tys <- mapM get xs
       ; when (not ((length xs) == (length fs)))
              (failD 2 [Ds "Unknown var in pattern."])
       ; return tys }
  where get x = case lookup x fs of
                  Nothing -> failD 2 [Ds "Unused formal parameter: ",Dd x]
                  Just (ty,_,_) -> return ty

-- Generate a reasonable error message when Skolem vars escape

escapes :: TyCh m => [(String,Sigma,[TcTv])] -> [TcTv] -> m ()
escapes trips [] = return ()
escapes trips bad = do { as <- getBindings
                       ; (display,lines) <- foldrM (f as) (initDI,"") bad
                       ; failDd 2 display [Ds lines] }
  where f as (Tv _ (Rigid All loc s) k) (d1,str) = return $
           displays d1 [Ds ("At "++show loc++" the explict typing: "++s)
                       ,Ds " is not polymorphic enough.", Ds str]
        f as (v@(Tv _ (Rigid Ex loc s) k)) (d1,str) =
          do { (d2,var) <- get d1 v trips
             ; return $
                displays d2 
                  [Ds "\nAn existential type var: ", Dd v
                  ,Ds ("\narising from the pattern: "++s)
                  ,Ds (" at "++show loc)
                  ,Ds "\nescapes into the environment in the type of ",Dd var]}
        get d1 v [] = return (d1,"")
        get d1 v ((name,typ,vs):xs) =
            do { t <- zonk typ
               ; if v `elem` vs
                    then return(displays d1 [Ds name,Ds " : ",Dd t])
                    else get d1 v xs }

escapeCheck :: (TyCh m,Show a) => a -> Rho -> Frag -> m ()
escapeCheck term typ (Frag _ skolvars _ _ _) = 
 do { resultVars <- get_tvs typ
    ; let bad = filter (`elem` resultVars) skolvars
    ; when (not (null bad)) 
           (escapes [("the exp\n   "++show term,(Forall (Nil([],typ))),bad)] bad)
    }

-----------------------------------------------------------------

fragMGU :: String -> Frag -> TC([Pred],MGU)
fragMGU info (Frag _ _ _ eqs rs) = handleM 3 (mguM eqs) err
  where err d1 mess = failDd 2 d1
               [Ds "Couldn't build unifier for: "
               ,Dl eqs ", "
               ,Ds (" because "++info++" "++mess)]
         

underLam :: Frag -> String -> TC a -> TC a
underLam frag p x = do { (_,ans) <- underLamGetPred frag p x; return ans}

underLamGetPred :: Frag -> String -> TC a -> TC([Pred], a)
underLamGetPred frag p x =  
   do { (preds,unifier) <- fragMGU p frag
      ; ans <- under (lambdaExtend preds unifier) p frag x
      ; return(preds,ans) }                        

underLet :: String -> Frag -> TC a -> TC a
underLet s frag x = do { (_,ans) <- underLetGetPred s frag x; return ans}
                      
underLetGetPred :: [Char] -> Frag -> TC a -> TC([Pred],a)
underLetGetPred s frag x = 
  do { (preds,unifier) <- fragMGU s frag
     ; ans <- under (letExtend preds unifier) s frag x
     ; return(preds,ans)
     }

prefix [] xs = True
prefix (x:xs) (y:ys) | x==y = prefix xs ys
prefix _ _ = False


underErr1 patvars (info@(DI (pairs,_))) message = failP 3 info newmessage
  where bad = concat [ match dispv patv | dispv <- pairs, patv <- patvars]
        match (m,freshname) (Tv n (Rigid Ex loc s) k) | m==n = [(freshname,loc,s)]
        match _ _ = []
        newmessage = message ++ concat(map report bad)
        report (name,loc,s) =
           "\nAn existential type var: "++name++
           "\n  arising from the pattern: "++s++" at "++show loc++" escapes"

getVarsFromEnv = do { env <- getGenerics; foldrM f ([],[]) env }
  where f (name,typ) (vars,trips) =
          do { vs <- get_tvs typ
             ; if null vs 
                  then return (vars,trips)
                  else return(vs++vars,(show name,typ,vs):trips) }

-- HERE ### 
under :: (Frag -> b -> TC c) -> String -> Frag -> b -> TC c
under extend p frag@(Frag xs patVars tenv eqs rs) comp =
  do { assump <- getAssume  -- Truths we already know, "eqs" are truths we will add
     ; (a,oblig) <- handleM 3 (collectPred(extend frag comp)) (underErr1 patVars)
     ; (residual,unifier) <- handleM 1 (mguM oblig) (underErr frag p assump oblig)
     ; when False -- (p=="(L ws)")
            (warn [Ds ("\nunder "++p)
                  ,Ds "\noblig = ", Dd oblig
                  ,Ds "\nresidual = ", Dd residual
                  ,Ds "\nunifier = ", Dd unifier
                  ,Ds "\neqs = ",Dd eqs
                  ,Ds "\nassump = ",Dd assump] >> return())
     ; let truths = (eqs++assump)
     ; unsolved <- solvePred truths residual
     --; outputString("\ntruths = "++show truths++"\nunsolved = "++show unsolved)                       
     ; (bad,passOn) <- splitObligations unsolved patVars
     --; outputString("\npass On = "++show passOn) 
     ; when (not (null bad)) 
            (failD 2 
              [Ds "\nIn the scope of the patterns: ",Ds p
              ,Ds "\nUnder the assumptions:\n   "
              ,Dl truths ", "
              ,Ds "\nWe could not solve the obligations:\n   "
              ,Dl residual ", "
              ,Ds "\nBecause after simplification we were left with:\n   "
              ,Dl bad ", "])

     ; (envVars,triples) <- getVarsFromEnv
     ; let bad = filter (`elem` envVars) patVars
     ; when (not (null bad)) (escapes triples bad)
     ; injectAccum passOn
     ; return a
     }



underErr frag pat assump oblig info s = 
   showFrag "UnderErr" frag >> 
   failDd 2 info
     [Ds ("\nWhile type checking in the scope of\n   "++pat)
     ,Ds "\nWe need to prove\n   ",Dd oblig
     ,Ds  "\nFrom the bindings\n   ", Dd assump
     ,Ds "\nBut ",Ds s]


splitObligations :: [Pred] -> [TcTv] -> TC([Pred],[Pred])
splitObligations need patVars = do { xs <- mapM f need; return(split xs ([],[])) }
  where f x = do { vs <- get_tvs x; return (x,vs) }
        split [] pair = pair
        split ((x,vs):xs) (yes,no) =
           split xs (if any (`elem` patVars) vs then (x:yes,no) else (yes,x:no))

--------------------------------------------------------------------------

peek :: TC a -> TC (a,[Pred])
peek x = do { (a,eqs) <- collectPred x; injectAccum eqs; return(a,eqs) }

instance Typable (Mtc TcEnv Pred) (Body Exp) Rho where
  tc (Normal e) expect = 
     do { --outputString ("\n Inside check body "++ show e++" :: "++show expect)
        ; e' <- tc e expect
        ; return(Normal e')}
  tc (Guarded xs) expect = do { xs' <- mapM f xs; return(Guarded xs')}
     where f (test,body) = binaryLift (,) (check test (Rtau boolT)) 
                                     (tc body expect)


------------------------------------------------------------------
-- This instance useable for (Fun matches)
-- f :: d1 -> d2 -> rng
-- f p1 p2 = e    leads to a call like:
-- tc (line 1, [p1,p2],Normal e,[]) (Check (d1 -> d2 -> rng))

-- ###

instance Typable (Mtc TcEnv Pred) (Match [Pat] Exp Dec) Rho where
  tc (loc,ps,body,ds) (Check t) = newLoc loc $
     do { (frag1,ps1,rng) <- checkBndrs localRename ps t
        ; t11 <- zonk t
        ; when False -- (interesting frag1)
           (showFrag ("\nIn Fun Match, t = "++show t11++"\nps = "++show ps++"\n") frag1)
        ; let err dis s  =
               (do { (Frag zs _ _ ts rs) <- zonk frag1
                   ; truths <- getBindings
                   ; failDd 3 dis
                       [Ds "\n*** Error in clause: "
                       ,Dl ps " ",Ds " = ",Ds (show body), Ds ":\n    ",Dd t
                       ,Ds "\n*** with\n   ",Dlf dispBind zs ", "
                       ,Ds "\n*** where ", Dl (subPred truths ts) ", "
                       ,Ds s]} )

        ; (_,frag2,ds2) <- underLam frag1 ("fun "++(show ps)++" where ...") 
                                   (inferBndr localRename ds)
        ; body3 <- handleM 2 (underLet ("fun "++(show ps)++" = "++show body++" :: "++show rng) 
                                       frag2
                                       (underLam frag1 (show ps) 
                                                 (hasMonoTypeest body rng))) err
        ; escapeCheck body t frag1
        ; return(loc,ps1,body3,ds2) }
  tc (loc,ps,body,ds) (Infer ref) = newLoc loc $
     do { (ts,frag1,ps1) <- inferBndrs localRename ps
        ; (_,frag2,ds2) <- underLam frag1 (show ps) 
                                    (inferBndr localRename ds)
        ; (rng,body3) <- underLet "MatchInfer" frag2
                                  (underLam frag1 (show ps) (infer body))
        -- ESCAPE CHECK
        ; escapeCheck body rng frag1
        ; let t = foldr arrow rng ts
        ; writeRef ref t
        ; return(loc,ps1,body3,ds2) }

hasMonoTypeest body rng =
  do { --outputString ("\n body = "++show body)
     --; outputString ("range = "++show rng)
     --; showSome ["zs","d","f","x"];
       check body rng }

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

instance Typable (Mtc TcEnv Pred) (Match Pat Exp Dec) Rho where
  tc (loc,p,body,ds) (Check t) = newLoc loc $
     do { ((dom,rng),obs) <- collectPred (unifyFun t)
        --; outputString ("After unifyFun "++show dom++" -> "++show rng)
        ; (frag1,p1) <- checkBndr localRename p dom
        -- ; showFrag ("\nUnder pat: "++show p++": "++show dom) frag1
        ; let err dis s  =
	       (do { (Frag zs _ _ ts rs) <- zonk frag1
	           ; truths <- getBindings
	           ; failDd 2 dis
	              [Ds ("\n*** Error in clause: "++show p++" -> "++show body++ "  :  "),Dd t
	              ,Ds "\n*** with  ",Dlf dispBind zs "\n         "
	              ,Ds "\n*** where ",Dl (subPred truths ts) ", "
	              ,Ds s]})
        ; (_,frag2,ds2) <- underLam frag1 (show p) (inferBndr localRename ds)
        ; body3 <- handleM 4 (underLet "CaseCheck" frag2(underLam frag1 (show p) (check body rng))) err
        ; escapeCheck body t frag1
        ; return(loc,p1,body3,ds2) }
  tc (loc,p,body,ds) (Infer ref) = newLoc loc $
     do { (dom,frag1,p1) <- inferBndr localRename p
        ; (_,frag2,ds2) <- underLam frag1 (show p) (inferBndr localRename ds)
        ; (rng,body3) <- underLet "CaseInfer" frag2(underLam frag1 (show p) (infer body))
        -- ESCAPE CHECK
        ; escapeCheck body rng frag1
        ; writeRef ref (arrow dom rng)
        ; return(loc,p1,body3,ds2) }

----------------------------------------------------------------
-- The main workhorse which does Exp. This is modelled after the
-- function in "Practical type inference for arbitrary-rank types"
-- by Simon Peyton Jones and Mark Shields

instance Typable (Mtc TcEnv Pred) Exp Rho where
  tc (Lit x) expect = do { x' <- tc x expect; return (Lit x') }
  tc (Var v) expect =
     do { m <- getLevel
        --; when (show v=="xyz") (outputString ("Checking variable "++show v))
        ; (sigma,n,exp) <- lookupVar v
        ; when (n > m) (failD 2 [Ds (show v++" used at level "++show m++" but defined at level "++show n)])
        --; when (show v=="xyz") $ outputString ("Sigma = "++show sigma++"\nExpect = "++show expect)
        ; morePoly (Var v) sigma expect
        --; when (show v=="xyz") $ outputString ("Poly check succeeds"++show sigma)
        ; return exp }

  tc (Sum inj x) (Check (Rsum t1 t2)) = -- t1 or t2 or both are non-trivial Sigmas
     do { (sig::Sigma,e) <- infer x
        ; case inj of { L -> morepoly sig t1; R -> morepoly sig t2 }
        ; return (Sum inj e) }
  tc (Sum inj x) expect =
     do { (a,b) <- expecting "Sum" tsum expect
        ; e <- check x (case inj of { L -> a; R -> b })
        ; return(Sum inj e) }

  tc (Prod x y) (Check (Rpair t1 t2)) = -- t1 or t2 or both are non-trivial Sigmas
     do { (s1::Sigma,e1) <- infer x
        ; (s2::Sigma,e2) <- infer y
        ; morepoly s1 t1
        ; morepoly s2 t2
        ; return (Prod e1 e2) }
  tc (Prod x y) expect =
     do { (a,b) <- expecting "Pair" tpair expect
        ; e1 <- check x a
        ; e2 <- check y b
        ; return (Prod e1 e2) }

  tc (e@(App fun arg)) expect =
     do { (fun_ty,f) <- infer fun
        ; (arg_ty, res_ty) <- handleM 2 (unifyFun fun_ty) (notfun e fun_ty)
        --; when (show arg == "ff")
        --       (warn [Ds ("In App ("++show e),Ds ")\narg_ty = ",Dd arg_ty,Ds "\nres_ty = ",Dd res_ty] >> return ())
        ; x <- handleM 2 (check arg arg_ty) (badarg e arg_ty)
        ; zz <- zonk arg_ty
        ; ns4 <- morePoly e res_ty expect
        ; return(App f x) }
  tc (exp@(Lam ps e _)) (Check t) =
     do { (frag,ps2,result) <- checkBndrs localRename ps t
        ; e2 <- underLam frag (show ps) (check e result)
        ; escapeCheck exp t frag
        ; return(Lam ps2 e2 []) }
  tc (exp@(Lam ps e _)) (Infer ref) =
     do { (ts2,frag,ps2) <- inferBndrs localRename ps
        ; (t,e2) <-  underLam frag (show ps) (infer e)
        -- ESCAPE CHECK
        ; escapeCheck exp t frag 
        ; writeRef ref (foldr arrow t ts2)
        ; return(Lam ps2 e2 []) }
  tc term@(Ann body pt) exp_ty =
     do { (ann_ty,_) <- checkPT pt
        ; exp <- check body ann_ty
        ; morePoly term ann_ty exp_ty
        ; return (Ann exp pt) }
  tc (Let ds e) expect =
     do { (_,frag,ds2) <- inferBndr localRename ds
        ; e2 <- underLet "LetExp" frag (tc e expect)
        ; return(Let ds2 e2)}
  tc (Circ vs e ds) expect = tcCircuit vs e ds expect      
  tc (Case exp ms) (Check rng) =
     do { --outputString "IN CASE";
          (dom,e2) <- infer exp
        --; showSome ["zs"]
        --; outputString (show dom)
        ; ms2 <- checkL ms (arrow dom rng)
        ; return(Case e2 ms2) }
  tc (Case exp ms) (Infer ref) =
     do { rng <- newRho star
        ; (dom,e2) <- infer exp
        ; ms2 <- checkL ms (arrow dom rng)
        ; writeRef ref rng
        ; return(Case e2 ms2) }
  tc (Do ss) expect =
      do { (m,b) <- unifyMonad expect
         ; (bindSig,bn,bexp) <- lookupVar (Global "bind")
         ; (failSig,fn,fexp) <- lookupVar (Global "fail")
         ; bindt <- bindtype m
         ; failt <- failtype m
         ; morepoly bindSig bindt
         ; morepoly failSig failt
         ; ss2 <- tcStmts m b ss
         ; return(Do ss2)}
  tc (CheckT e) expect =
     do { ty <- case expect of { Check t -> return t; Infer ref -> readRef ref }
        ; ts <- getBindings
        ; assumptions <- getAssume
        ; truths <- zonk ts
        ; typ <- zonk ty
        ; d1 <- getDisplay
        --; outputString ("\nDisplay = "++show d1)
        ; let (eD) = show e
              (d2,typD) = disp d1 typ
              (d3,eqnD) = deqs d2 truths
              (d4,assumeD) = dispL disp d3 assumptions ", "
        ; outputString ("\n*** Checking: " ++ eD ++
                   "\n*** expected type: " ++ typD ++
                   "\n***         Where: " ++ eqnD ++
                   "\n***        Truths: "++ assumeD)
        ; env <- tcEnv
        ; checkLoop typ d4 env
        ; x <- tc e expect 
        ; return(CheckT x)}
  tc (Lazy e) expect = do { x <- tc e expect; return(Lazy x)}
  tc (Exists e) (Check (Rtau (TyEx xs))) = 
     do { (preds,tau) <- instanL xs  -- ## WHAT DO WE DO WITH THE PREDS?
        ; tc e (Check (Rtau tau))}
  tc (p@(Exists e)) expect = 
    fail ("Existential expressions cannot have their type inferred:\n  "++show p++
          "\n Use a prototype. "++show expect)
  tc (Under e1 e2) expect = error "Under"
  tc (Bracket exp) expect =
     do { a <- unifyCode expect
        ; e <- levelInc (check exp a)
        ; return(Bracket e)}
  tc (Escape exp) expect =
     do { n <- getLevel
        ; case (n,expect) of
           (0,_) -> failD 2 [Ds ("Esc at level 0: "++show (Escape exp))]
           (_,Check t) ->
              do { e <- levelDec(check exp (tcode t)); return(Escape e)}
           (_,Infer ref) ->
              do { t <- newRho star
                 ; e <- levelDec (check exp (tcode t))
                 ; writeRef ref t
                 ; return(Escape e) }}
  tc (Run exp) (Check t) =
      do { e <- check exp (tcode t); return(Run e)}
  tc (Run exp) (Infer ref) =
      do { t <- newRho star
         ; e <- check exp (tcode t)
         ; writeRef ref t
         ; return(Run e) }
  tc (Reify s v) expect = error ("Unexpected reified value: "++s)


tcStmts m b [] = failD 2 [Ds "Do should have at least one statement"]
tcStmts m b [NoBindSt loc e] =
   do { e2 <- newLoc loc (check e (Rtau (TyApp m b)))
      ; return([NoBindSt loc e2])}
tcStmts m b [st@(BindSt loc pat e)] =
   failD 2 [Ds ("Last stmt in Do must not be a bind: "++show st)]
tcStmts m b [st@(LetSt loc ds)] =
   failD 2 [Ds("Last stmt in Do must not be Let: "++show st)]
tcStmts m b ((LetSt loc ds):ss) =
   do { (_,frag,ds2) <- inferBndr localRename ds
      ; ss2 <- underLet "LetStmt" frag (tcStmts m b ss)
      ; return((LetSt loc ds2):ss2)}
tcStmts m b ((NoBindSt loc e):ss) =
   do { a <- newTau star
      ; e2 <- check e (Rtau(TyApp m a))
      ; ss2 <- tcStmts m b ss
      ; return((NoBindSt loc e2):ss2)}
tcStmts m b ((BindSt loc pat e):ss) =
   do { a <- newTau star
      ; e2 <- check e (Rtau(TyApp m a))
      ; (frag,p2) <- checkBndr localRename pat (simpleSigma a)
      ; ss2 <- underLam frag (show pat) (tcStmts m b ss)
      ; return((BindSt loc p2 e2):ss2)}


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
  ((case (pt s1,pt s2) of
    (a@(Forallx All xs _ x),b@(Forallx All ys _ y)) ->
        do { (t1,_) <- checkPT a
           ; (t2,_) <- checkPT b
           ; b <- morepoly t1 t2; outputString (show b ++ "\n") }
    (a@(Forallx All xs _ x),y) ->
        do { (t1,_) <- checkPT a
           ; t2 <- toRho typeConstrEnv0 y
           ; b <- morepoly t1 t2; outputString (show b ++ "\n") }
    (x,y) ->
        do { t1 <- toRho typeConstrEnv0 x
           ; t2 <- toRho typeConstrEnv0 y
           ; b <- morepoly t1 t2; outputString (show b ++ "\n") }) :: TC ())


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


frag0 = Frag (map f vals) [] [] [] []
  where f (nm,(v,sigma)) = (Global nm,(sigma,0,Var (Global nm)))

initTcEnv = addFrag frag0 tcEnv0 


-- A version in the FIO monad that returns unresolved NEED as well
-- as the final TcEnv and the transformed Decs

checkDecs :: TcEnv -> [Dec] -> FIO (TcEnv,[Dec],[Pred])
checkDecs env ds = do { ((a,b),c) <- unTc (checkBndGroup ds) env; return(b,a,c)}

checkBndGroup :: [Dec] -> TC([Dec],TcEnv)
checkBndGroup [d@(TypeSyn loc nm args pt)] = 
  do { env <- tcEnv
     ; (argBinds,rng) <- newLoc loc (useSigToKindArgs 0 args Nothing)
     ; (_,argsAsNames,argEnv) <- argsToEnv argBinds []
     ; (tau,monoKind,kind) <- inferPT argEnv pt
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
     ; (preds,unifier) <- fragMGU "Checking declaration group" frag
     ; env <- letExtend preds unifier frag tcEnv
     ; return(ds2,refute env frag)
     }
checkBndGroup ds | all isKind ds =
  do { (sigma,frag,ds2) <- checkDataDecs kindStrata  (useTypeSig ds) -- inferBndr False ds
     ; (preds,unifier) <- fragMGU "Checking declaration group" frag
     ; env <- letExtend preds unifier frag tcEnv
     ; return(ds2,env)
     }     
checkBndGroup ds =
  do { (sigma,frag,ds2) <- inferBndr False ds
     ; (preds,unifier) <- fragMGU "Checking declaration group" frag
     ; env <- letExtend preds unifier frag tcEnv
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
          do { (nmType,monoKind,nmTypeKind) <- inferPT [] pt
             ; let poly = K(simpleSigma nmType)
             ; return (nm,TyCon (nm) poly,poly) }

hasMonoTypeypeFuns :: TcEnv -> [Dec] -> TC [(String,[Tau] -> TC Tau)]
hasMonoTypeypeFuns env [] = return []
hasMonoTypeypeFuns env1 (TypeFun loc nm (Just pt) ms : more) = 
  do { (nmType,monoKind,nmTypeKind) <- inferPT [] pt
     ; let poly = K(simpleSigma nmType)
           down (Karr x y) xs = down y (xs++[x])
           down rng xs = (rng,xs)
           (rng,ks) = down nmType []
     ; clauses <- mapM (checkLhsMatch (type_env env1) ks rng) ms
     ; morepairs <- hasMonoTypeypeFuns env1 more
     ; return ((nm,makeTfun nm poly clauses): morepairs)
     }

-- Successful kind-checking of a type function returns a [([Tpat],Tau)]
-- from this we must produce a function with type: [Tau] -> TC Tau. We do
-- this using two functions tmatch and teval

makeTfun :: String -> PolyKind -> [([Tpat],Tau)] -> ([Tau] -> TC Tau)
makeTfun s k [] = return . TyFun s k 
makeTfun s k ((ps,body):more) = f
  where f args = case matchmany ps args [] of
                   Just env -> teval env body 
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
tmatch (Tcon s []) (TyCon t k) env = if s==t then Just env else Nothing
tmatch (Tcon s ps) (app@(TyApp _ _)) env =
  do { let down (TyApp (TyCon s k) x) = return(s,[x])
           down (TyApp x y) = do { (c,ys) <- down x; return(c,ys++[y])}
           down y = Nothing
     ; (g,ys) <- down app
     ; if g==s then matchmany ps ys env else Nothing}
tmatch (Tfun s ps) (TyFun t _ xs) env | s==t = matchmany ps xs env   
tmatch x (TySyn nm n fs as y) env = tmatch x y env
tmatch (Tapp x y) (TyApp a b) env = do { e1 <- tmatch x a env; tmatch y b e1}
tmatch x (TyEx xs) env = error "Now matching for existentials yet"
tmatch x y env = Nothing     


{- ==============================================
teval :: [(Name,Tau)] -> Tau -> TC Tau
teval env (y@(TyVar nm k)) = 
   case lookup nm env of {Just x -> return x; Nothing -> return y}
teval env (TyApp x y) = 
   do { a <- teval env x; b <- teval env y; return(TyApp a b)}
teval env (TyCon s k) = return(TyCon s k) 
teval env (Star n) = return(Star n)
teval env (Karr x y) = 
   do { a <- teval env x; b <- teval env y; return(Karr a b)}
teval env (w@(TyFun f k xs)) = 
   do { pairs <- getTyFuns
      ; ys <- mapM (teval env) xs
      --; outputString ("\nNormalizing: "++show w)
      ; ans <- case lookup f pairs of
                Just ffun ->  ffun ys
                Nothing -> return(TyFun f k ys)
      --; outputString ("To get: "++show ans)
      ; return ans }
teval env (TySyn nm n fs as x) = teval env x      
teval env (TyEx x) =  do { a <- tevalL env x; return(TyEx a) }
teval env x = return x         

-- nfL ::  TyCh m => L([Pred],Rho) -> m(L([Pred],Rho))
tevalL env xs = 
  do { let (ys,(eqn,t)) = unsafeUnwind xs
           f (nm,MK k,q) = do { a <- (teval env k); return (nm,MK a,q)}
     ; eqn2 <- mapM (tevalEq env) eqn
     ; ys2 <- mapM f ys
     ; t2 <- teval env t
     ; return(windup ys2 (eqn2,t2))
     }

tevalEq env (Equality x y) = 
     do { a <- teval env x; b<- teval env y; return(Equality a b)}
tevalEq env (Rel nm ts) =
     do { ys <- teval env ts; return(Rel nm ys) }

tevalRho env (Rtau x) = do { a <- teval env x; return(Rtau a) }
tevalRho env (Rarrow s r) = 
  do { a <- tevalSig env s; b <- tevalRho env r; return(Rarrow a b)}
tevalRho env (Rpair s r) = 
  do { a <- tevalSig env s; b <- tevalSig env r; return(Rpair a b)}
tevalRho env (Rsum s r) = 
  do { a <- tevalSig env s; b <- tevalSig env r; return(Rsum a b)}

tevalSig env (Forall (Nil(eqn,r))) = 
  do { a <- mapM (tevalEq env) eqn; b <- tevalRho env r
     ; return(Forall(Nil(a,b)))}
tevalSig env x = fail ("Sigma type: "++show x++" in existential.")     
--==================================================
-}


-- check the lhs (i.e. {plus (S x) y} = ... ) of each match

checkLhsMatch :: ToEnv -> [Tau] -> Tau -> ([PT],PT) -> TC ([Tpat],Tau)
checkLhsMatch current ks range (ps,rhs) = 
  do { (_,pats) <- thrd [] pTtoTpat (tail ps)   -- ps = {plus (S x) y} throw away "plus"
     ; envs <- mapM (checkPTBndr current) (zip pats ks)
     ; let newenv = concat envs ++ current
     ; rhsTau <- toTau newenv rhs
     ; w <- check rhsTau range
     ; return(pats,w)
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

----------------------------------------------------------
-- This code is used to translate a sigma type into a rule.
-- given (forall a . P a => T a -> S a -> Q a)
-- We need to test that T,S, and Q are all Proposition constructors.
-- The rule would be  Q a -> T a, S a  When P a
-- we need to translate (Q a) into a pattern so that we can
-- match Propositions against it to obtain a binding for "a"

-- Some example rules
-- ("trans"        ,[c],False,LE a b   ,[],[LE a c,LEc b])
-- ("equalCommutes",[] ,True ,Equal a b,[],[Equal b a])
--  name    uninstan^  permutes LHS    cond  RHS
type Rule = (Tau,String,[(Name,Kind)],Bool,Tpat,[(String,Tpat,Pred)],[Pred])


instance TypeLike (Mtc TcEnv Pred) Rule where
  sub env (b1,name,f,b,tpat,preds,rules) =
   do { p2 <- mapM (subP env) preds; r2 <- sub env rules; return(b1,name,f,b,tpat,p2,r2)}
    where subP env (nm,pat,pred) = do { pred2 <- sub env pred; return(nm,pat,pred) }
  zonk (b1,name,f,b,tpat,preds,rules) =
   do { p2 <- mapM zonkP preds; r2 <- zonk rules; return(b1,name,f,b,tpat,p2,r2)}
    where zonkP (nm,pat,pred) = do { pred2 <- zonk pred; return(nm,pat,pred) }
  get_tvs f = error "No way to get the type vars from a Rule"
  nf x = error "Can't put Rules in normal form"
  
tau2Tpat :: TyCh m => Tau -> m Tpat
tau2Tpat (TyVar nm k) = return(Tvar (show nm) nm)
tau2Tpat (TyApp x y) = 
  do { dom <- tau2Tpat x
     ; rng <- tau2Tpat y
     ; return(Tapp dom rng)}
tau2Tpat (TyCon s k) = return(Tcon s [])
tau2Tpat (Star n) = return(Tstar n)
tau2Tpat (Karr x y) = 
  do { dom <- tau2Tpat x 
     ; rng <- tau2Tpat y 
     ; return(Tkarr dom rng)}
tau2Tpat (TySyn s n fs as x) = tau2Tpat x
tau2Tpat x = failD 0 [Ds "The type: ",Dd x,Ds " is not appropriate for a proposition."]


splitIntoPredsRho s = 
  do { x <- instanTy s             -- The instanTy, generalize sequence
     ; sig@(Forall y) <- generalize x    -- removes Equality predicates
     ; (_,rho) <- instanTy sig
     ; (_,z) <- unwind y
     ; return (z,rho)
     };

isRuleCon :: String -> TC Bool -- Is the name of a TyCon 
isRule "Equal" = return(True)  -- the name of a Proposition?
isRuleCon s = 
 do { env <- tcEnv;
    ; return(elemFM s (rules env))
    }

rootPropM s (TyApp f y) = rootPropM s f 
rootPropM s (TyCon nm k) = return nm
rootPropM s x = failD 2 [Ds "\nNon Type constructor: "
                       ,Dd x
                       ,Ds " used as Prop in:\n  "
                       ,Dd s]

isPropM :: Rho -> [String] -> Tau -> TC Pred
isPropM sigma new t = 
  do { s <- rootPropM sigma t; 
     ; if elem s new
          then return (Rel s t)
          else ifM (isRuleCon s)
                   (return (Rel s t))
                   (failD 2 [Ds "\nThe type: ("
                            ,Dd t
                            ,Ds ") is not a proposition."
                            ])}

------------------------------------------------------------------
-- This code tests the type of a function to see if it could
-- be a theorem. It can't irrevocably fail, since most functions
-- are not theorems

rootProp (TyApp f y) = rootProp f 
rootProp (TyCon nm k) = Just nm
rootProp x = Nothing

isProp:: String -> Tau -> TC Bool
isProp new t = 
  case rootProp t of
   Just s | s==new -> return True
   Just s -> isRuleCon s
   Nothing -> return False

getDomsRng (Rtau z) = Just(down [] z)  
  where down xs (TyApp (TyApp (TyCon "(->)" _) x) y) = down (x:xs) y
        down xs z = (reverse xs,z)
getDomsRng r = Nothing


addTheorem :: String -> Frag -> Sigma -> TC Frag
addTheorem fname (frag@(Frag vs exs ts toenv rules)) sig = 
  do { ((preds,rho),lhsRho) <- splitIntoPredsRho sig
     ; always <- newTau star
     ; case okRho rho of
        Just (tname,doms,rng) -> 
            ifM (allM (isProp "") (rng:doms))
                (do { r <- sigmaToRule [] always fname preds rho
                    ; return(Frag vs exs ts toenv (r:rules))
                    })
                (return frag)
        Nothing -> return frag
     }
     
okRho :: Rho -> Maybe(String,[Tau],Tau)
okRho rho = 
  do { (doms,rng) <- getDomsRng rho
     ; tname <- rootProp rng
     ; return(tname,doms,rng)}

-------------------------------------------------------------------
--- To refute a proposition, show that it does not unify with any
-- of the LHS's of the defining rules.

refute env (Frag _ _ _ _ rules) = newenv where
  eqf (x,r1) (y,r2) = x==y
  lists = map f (groupBy eqf rules) -- [(propName,[LHS])]
  get_pats (propName,(lhs,rulename,free,permutes,tpat,conds,rhs)) = lhs
  f (rs@((propName,_):_)) = (propName,map get_pats rs) 
  computeFun (propName,lhss) = (propName,lhsUnify lhss)
  lhsUnify [] x = failD 0 [Ds "The proposition: (",Dd x,Ds ") can never be solved."]
  lhsUnify (lhs:lhss) x = 
     case mgu [(lhs,x)] of
       Left _ -> return () 
       Right (s,a,b) -> lhsUnify lhss x
  newenv = env { refutations = addListToFM (refutations env) (map computeFun lists)}
       
-----------------------------------------------------------
  
sigmaToRule :: [String] -> Tau -> String -> [Pred] -> Rho -> TC(String,Rule)
sigmaToRule mutRecPropList lhsTau name preds rho = 
  do { (doms,rng) <- splitRho rho
     ; tname <- rootPropM rho rng
     ; pat <- tau2Tpat rng
     ; results <- mapM (isPropM rho mutRecPropList) doms
     ; let vs = uninstanVars preds doms rng
           fix (r@(Rel s t)) = do { p <- tau2Tpat t; return(s,p,r)}
     ; conds <- if null vs 
                   then mapM fix preds
                   else mapM fix (preds++results)
     ; let rhs = if null vs then results else []
           rule = (lhsTau,name,vs,False,pat,conds,rhs)
     ; return(tname,rule)}

uninstanVars preds doms rng = deleteFirstsBy f (unionBy f pvs dvs) rvs
  where (_,pvs) = varsOfPred preds
        (_,dvs) = foldr g ([],[]) doms
        g t vs = union2 (varsOfTau t) vs
        (_,rvs) = varsOfTau rng
        f (n1,k1) (n2,k2) = n1==n2


-- splitRho(S a -> T a -> Q a) = ([S a,T a],Q a)
splitRho (Rtau z) = return(down [] z)  
  where down xs (TyApp (TyApp (TyCon "(->)" _) x) y) = down (x:xs) y
        down xs z = (reverse xs,z)
splitRho r = failD 1 [Ds "Non trivial rho type in proposition: ",Dd r]

-- Using rules

type Unifier = [(Name,Tau)] 

possibleUnifiers :: Unifier -> [Pred] -> Tpat -> [Unifier]
possibleUnifiers unifier [] pat = []
possibleUnifiers unifier ((Equality _ _):truths) pat = possibleUnifiers unifier truths pat
possibleUnifiers unifier ((Rel nm t):truths) pat =
  let rest = possibleUnifiers unifier truths pat
  in case tmatch pat t unifier of
      Just u -> u:rest
      Nothing -> rest

-------------------------------------------------------------------
findInstances :: [Pred] -> [([Char],Tpat,Pred)] -> Unifier -> [Unifier]
findInstances truths [] unifier = [unifier]              
findInstances truths ((nm,tpat,pred):pats) unifier = concat uss
  where us = possibleUnifiers unifier truths tpat
        uss = map (findInstances truths pats) us
  
covers :: Unifier -> [(Name,Kind)] -> Bool
covers unifier [] = True
covers unifier ((m,k):missing) = 
  case lookup m unifier of
    Just t -> covers unifier missing
    Nothing -> False


freshCond :: [(Name,Kind)] -> [Pred] -> [(String,Tpat,Pred)] -> 
             [(Name,Tau)] -> TC [(Unifier,[Pred])]
freshCond [] truths conds unifier = 
  do { x <- freshC conds unifier; return[x]}
freshCond missing truths conds unifier = 
  do { let possibleU = findInstances truths conds unifier
           unifiers = filter (\ u -> covers u missing)  possibleU
     ; mapM (freshC conds) unifiers }

freshC conds u =
  do { c <- sub (u,[],[]) (map (\(n,p,r) -> r) conds)
     ; return(u,c)}

nullM x y z = do { xs <- x; if null xs then y else z}



solveNotEqual:: Tau -> Tau -> TC(Maybe[Pred])
solveNotEqual x y =
  case mgu [(x,y)] of 
    Left [] -> return Nothing
    Left [(v,t)] -> return Nothing -- (Just[Rel "(!=)" (notEq (TcTv v) t)])
    Left xs -> failD 1 [Ds "More than one residual in in-equality",Dl xs ", "]
    Right _ -> return (Just[])
    
solveEqual:: Tau -> Tau -> TC(Maybe[Pred])
solveEqual x y =
  do { a <- nf x; b <- nf y
     ; let f (v,e) = equalRel (TcTv v) e
     ; case mgu [(a,b)] of 
        Left [] -> return(Just [])
        Left xs -> return Nothing
        Right(s,m,n) -> failD 3 [Ds "The Equality constraint: "
                                ,Dd x, Ds " = ",Dd y
                                ,Ds "Cannot be solved\n"
                                ,Ds s]}

useRule :: [Pred] -> [Rule] -> Tau -> TC(Maybe[Pred])
useRule truths rules (TyApp (TyApp (TyCon "(!=)" k) x) y) = solveNotEqual x y
useRule truths rules (TyApp (TyApp (TyCon "Equal" k) x) y) = solveEqual x y
useRule truths [] t = return Nothing
useRule truths ((conP,name,free,permutes,pat,conds,results):rs) t = 
  case tmatch pat t [] of
    Just unifier -> 
      do { choices <- freshCond free truths conds unifier
         ; let try [] = useRule truths rs t
               try ((u,cs):xs) = 
                 nullM (handleM 9 (solvePred truths cs)
                                  (\ _ _ -> return[Rel "DUMMY" t]))
                       (fmap Just (sub(u,[],[])results))
                       (try xs)
         ; try choices}
    Nothing -> useRule truths rs t

useRuleMany truths rules name t = 
  do { zs <- useRule truths rules t
     ; case zs of
         Just residual -> solvePred truths residual
         Nothing -> return[Rel name t]
     }

instance Eq Pred where
  (Equality a b) == (Equality x y) = a==x && b==y
  (Rel s x) == (Rel t y) = s==t && x==y
  _ == _ = False


solveConstraints :: [Pred] -> [Pred] -> TC [Pred]
solveConstraints truths cs =
  do { (residual,unifier) <- (mguM cs)
     ; solvePred truths residual
     }

    
solvePred :: [Pred] -> [Pred] -> TC [Pred]
solvePred truths [] = return []
solvePred truths ((r@(Rel s term)):ps) = 
  -- (warn [Ds "R = ",Dd r,Ds (sht term),Ds "\n truths are ",Dl truths ", "
  --       ,Ds (concat (map shtEq truths))]) >>
  if elem r truths
     then solvePred truths ps
     else do { refute <- getRefutation s
             --; warn [Ds "the term r = ",Dd r]
             ; rules <- getMatchingRules s
             --; warn [Ds "Matchning rules are: ",Dl rules ", "]
             ; t <- zonk term
             ; refute t
             ; xs <- useRuleMany truths rules s t
             --; warn [Ds "results of useRule ",Dd xs]
             ; ys <- solvePred truths ps
             ; xs2 <- removeAlreadyTrue truths xs
             ; return(xs2++ys)}
solvePred truths (p:ps) =  
  failD 1 [Ds "unknown predicate: ", Dd p]

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
oneMatch2 un1 ((Rel _ t):ts) (z@(Rel _ x)) =
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

--------------------------------------------
-- Exhibit Rule
instance NameStore d => Exhibit d Rule where
  exhibit d1 (conP,name,f,b,pat,conds,ps) = (d4,"\n"++name++": "++p2++" --> "++
                                        ps2++"\n   "++vs++" if "++c2)
    where (d2,p2,c2,ps2) = exhibit3 d1 (pat,map (\(n,p,r) -> r) conds,ps)
          (d3,f2) = exhibitL exhibitName d2 f ", "
          (d4,vs) = if null f then (d3,"") 
                       else (d3,"(Exists "++f2++") ")
                       
exhibitName d (nm,_)  = useStoreName nm star f d
    where f s = "'"++s  
             
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
checkPTBndr current (y@(Tcon c xs),k) = 
  do { (tau,kind@(K sigma)) <- getInfo y current c
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
checkPTBndr current (Tkarr x y,k) =
  do { env1 <- checkPTBndr current (x,k)
     ; env2 <- checkPTBndr current (y,k)
     ; return(env1++env2) }
checkPTBndr current (y,k) = 
  failD 1 [Dd y,Ds " :: ",Dd k,Ds " is not well formed for a lhs."]
                
     

----------------------------------------------------

testRankN :: [[Dec]] -> FIO([[Dec]])
testRankN dss = fio $ runTC tcEnv0 (letExtend [] [] frag0 (testBndGroups dss))

parseAndKind :: TcEnv -> [Char] -> FIO (Kind,Tau)
parseAndKind env s = tcInFIO env
    (
    do { map1 <- getTypeEnv
       ; s <- toTau map1 (pt s)
       ; (tau,s2) <- infer s
       ; return(MK tau,s2)
       })



testBndGroups :: [[Dec]] -> TC [[Dec]]
testBndGroups [] = return []
testBndGroups (ds:dss) =
  do { outputString ("Group Binds" ++ show(concat (map decname ds)));
       env <- getTypeEnv
     --; mapM g7 env
     ; (sigma,frag,ds2) <- inferBndr False ds
     --; showFrag "" frag
     ; (preds,unifier) <- fragMGU "checking testBndGroups" frag
     ; dss2 <- letExtend preds unifier frag (testBndGroups dss)
     ; return(ds2:dss2)
     }

arrowP (Rarrow _ _) = True
arrowP (Rtau (TyApp (TyApp (TyCon "(->)" k) x) y)) = True
arrowP _ = False

wellTyped :: TcEnv -> Exp -> FIO(Sigma,Exp)
wellTyped env e = tcInFIO env 
  (do { ((t::Rho,term),oblig) <- collectPred(infer e)
      ; oblig2 <- solvePred [] oblig
      ; typ <- nfRho t
      ; when (not(null oblig2) && not(arrowP typ))
             (failD 0 [Ds "Unresolved obligations: ",Dl oblig2 ", "])
      ; sigma <- generalize(oblig2,typ)
      ; return(sigma,term)})

ioTyped :: TcEnv -> Pat -> Exp -> FIO(Exp,Pat,TcEnv,Tau)
ioTyped env p e = 
  tcInFIO env 
    (do { a <- newTau star
        ; e' <- check e (Rtau (TyApp ioT a))
        ; (frag,p') <- checkBndr False p (simpleSigma a)
        ; a' <- zonk a
        ; return (e',p',addLetFrag frag env,a')
        })
                                

tcInFIO :: TcEnv -> TC x -> FIO x
tcInFIO env e =
  do { (x,ns::[Pred]) <- unTc e env
     ; if null ns
          then return x
          else fail ("\nUnresolved NEED: "++show ns)}

showFrag message frag =
  do { (Frag xs rs tenv eqs rules) <- zonk frag
     ; outputString ("\n********** Frag ***************" ++ message ++
           "\nBindings = "++plistf showBind "" (take 5 xs) ", " ""++
           "\nSkolem = "++show rs++
           "\nTypeEnv = "++ show tenv++
           "\nPreds = "++showPred eqs++"\n*********************") }

showBind (x,(t,_,_)) = show x ++":"++show t
dispBind d (x,(t,_,_)) = displays d [Dd x,Ds ":",Dd t]

g7 (s,t,k) = outputString ("type "++s ++" : " ++ alpha [] k)

----------------------------------------------------------------------

interactiveLoop :: String -> (env -> state -> TC(state,Bool)) -> env -> state -> TC()
interactiveLoop prompt f env info = handleM 3
  (do { outputString prompt
      ; (info2,continue) <-  (f env info)
      ; if continue then interactiveLoop prompt f env info2 else return ()
      }) (\ dis s -> do {outputString s; interactiveLoop prompt f env info})



putS s = Tc h
  where h env = fio(putStrLn s >> return((),[]))
getS = Tc h
  where h env = fio(do { (s::String) <- getLine; return(s,[])})

checkReadEvalPrint :: (Rho,TcEnv) -> DispInfo -> TC (DispInfo,Bool)
checkReadEvalPrint (hint,env) info =
  do { input <- getS
     ; z <- parseString pCommand (backspace input [])
     ; case z of
        Left s -> do {putS s; return (info,True) }
        Right(x,rest) ->
         case x of
          (ColonCom "q" _) -> return (info,False)
          (ColonCom "e" _) -> 
             do { truths <- zonk (bindings env)
                ; let (info2,estring) = disp info truths
                ; putS(estring)
                ; return (info2,True) }
          (ColonCom "h" _) ->
             do { let (info2,tstring) = disp info hint
                ; putS("Hint = "++tstring)
                ; return(info2, True)
                }
          (ColonCom "k" x) ->
	     do { (k,t) <- getkind x env
	        ; putS (x++" :: "++(pprint k)++"  = " ++ pprint t)
                ; return (info,True) }
          (ColonCom "t" x) ->
	     case getVar (Global x) env of
	        Just(sigma,lev,exp) ->
	           do { s1 <- zonk sigma
	              ; putS (x++" :: "++(pprint s1)) -- ++"\n"++sht t)
	              ; return (info,True)}
                Nothing -> do { putS ("Unknown name: "++x); return (info,True)}
          (ColonCom "o" e) ->
             do { exp <- getExp e
                ; (t::Sigma,_) <- infer exp
                ; t1 <- zonk t
                ; putS(show exp ++ " :: " ++ pprint t1)
                --; occursWhere env t
                ; return (info,True)
                }
          (ExecCom exp) ->
             do { ((t::Rho,_),oblig) <- collectPred(inDisplay info (infer exp))
                ; t2 <- zonk t
                ; obs <- zonk oblig
                ; let (info2,tstring,eqs) = disp2 info (t2,obs)
                ; putS(show exp ++ " :: " ++ tstring)
                ; when (not (null oblig))
                       (putS ("Only when we can solve\n   "++eqs))
                --; occursWhere env t
                ; return (info2,True)
                }
          other -> putS "unknown command" >> return (info,True)
     }

checkLoop :: Rho -> DispInfo -> TcEnv -> TC ()
checkLoop typ d env = interactiveLoop "check>" checkReadEvalPrint (typ,env) d


---------------------------------------------------------
-- display names in a more readable manner by maintaining
-- a list of readable names for each Var encountered.

inDisplay :: DispInfo -> TC a -> TC a
inDisplay disp (Tc f) = Tc g
  where g env = f (env{displayInfo = disp})


instance NameStore d => Exhibit d [(Var,(Sigma,Level,Exp))] where
  exhibit xs [] = (xs,"")
  exhibit xs ys = exhibitL exhibit xs ys "\n   "

instance NameStore d => Exhibit d (Var,(Sigma,Level,Exp)) where
  exhibit xs (v,(s,l,e)) = (zs,show v++": "++ans)
   where (zs,ans) = exhibit xs s


---------------------------------------------------------------------
-------------------------------------------------------------------
-- Printing out tables for the manual

infixOperators = (concat (map f metaHaskellOps))
  where f x = case lookup x vals of
                 Nothing -> []
                 Just (_,y) -> [(x,show y)]
  
main2 = show_init_vals "D:/work/papers/OmegaManual/kinds.tex" "D:/work/papers/OmegaManual/types.tex"

show_init_vals :: String -> String -> IO()
show_init_vals kindfile prefixfile = go
  where f ("unsafeCast",_) = ""
        f ("undefined",_) = ""
        f (x,(y,z)) = (g x ++ " :: " ++ show z ++ "\n")
        hf (x,y,z) = (g x ++ " :: " ++ show z ++ "\n")
        hg (x,y) = "("++x++") :: " ++ show y ++ "\n"
        g [] = []
        g "[]" = "[]"
        g (s@(c:cs)) | isAlpha c = s         -- normal names
                     | c == '(' = s
                     | True = "("++s++")"    -- infix operators
        go = do { putStrLn "Writing tables for Manual"
                ; h <- openFile kindfile WriteMode
        
                ; hPutStr h "\\begin{figure}[t]\n"
	        ; hPutStr h "\\begin{multicols}{2}\n"
	        ; hPutStr h "{\\small\n\\begin{verbatim}\nType :: Kind \n\n"
	        ; hPutStr h (concat (map hf typeConstrEnv0))
                ; hPutStr h "\\end{verbatim}}\n"
	        ; hPutStr h "\\end{multicols}\n"
	        ; hPutStr h "\\caption{Predefined types and their kinds.}\\label{types}\n"
	        ; hPutStr h "\\hrule\n"
         
	        ; hPutStr h "\\begin{multicols}{2}\n"
                ; hPutStr h "{\\small\n\\begin{verbatim}\nValue :: Type \n\n"
                ; hPutStr h (concat (map f vals))
                ; hPutStr h "\\end{verbatim}}\n"
                ; hPutStr h "\\end{multicols}\n"
                ; hPutStr h "\\caption{Predefined functions and values.}\\label{values}\n"
		; hPutStr h "\\hrule\n"
                ; hPutStr h "\\end{figure}\n"
                ; hClose h
                
                
                ; h <- openFile prefixfile WriteMode
	        ; hPutStr h "\\begin{figure}[t]\n"
	        ; hPutStr h "\\begin{multicols}{2}\n"
	        ; hPutStr h "{\\small\n\\begin{verbatim}\nOperator :: Type \n\n"
	        ; hPutStr h (concat (map hg infixOperators))
		; hPutStr h "\\end{verbatim}}\n"
		; hPutStr h "\\end{multicols}\n"
		; hPutStr h "\\caption{The fixed set of infix operators and their types.}\\label{infix}\n"
	        ; hPutStr h "\\hrule\n"
	        ; hPutStr h "\\end{figure}\n"
                ; hClose h
                
                }
--------------------------------------------------------
-- INitializing the type environment
--------------------------------------------------------

---------------------------------------------------------------
---------------------------------------------------------------


trans0 s = (readName "In trans0: ") typeConstrEnv0 s   

{- 
parseSigma :: TyCh m => String -> m Sigma
parseSigma s = toSigma typeConstrEnv0 (pt s)

getrho :: TyCh m => [Char] -> m Rho
getrho s = toRho typeConstrEnv0 (pt s)
-}


toEnvX :: ToEnv
toEnvX = 
  [( "[]"     , listT,poly star_star)
  ,( "(,)"    , pairT, poly (karr star (star_star)))
  ,( "()"     , unitT, poly star)
  ,( "(->)"   , arrowT, poly (karr star (star_star)))
  ,( "Atom"   , atomT, kind4Atom)
  ,( "(+)" , sumT, poly (karr star (star_star)))
  ,( "(!=)", notEqT, notEqKind)
  ,( "Hidden" , hiddenT, kind4Hidden)
  ,( "String",stringT,poly star)
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
 "kind Nat = Z | S Nat\n"++
 "prop Nat' t = Z where t=Z | exists y . S (Nat' y) where t = S y\n"++
 "data Equal a b = Eq where a=b\n"++
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
        (dss,pairs) = topSortR freeOfDec ds

look = putStr (show (map (map f) preDefDec)) where f x = (show x) ++ "\n"

-- Go through each binding group in the topological sort
-- and transform the environment

decMany :: [[Dec]] -> TcEnv -> FIO TcEnv
decMany [] env = return env
decMany (ds:dss) env = 
  do { (env2,_,_) <- checkDecs env ds
     ; rt_env <- elaborate None ds (runtime_env env2)  -- evaluate the list
     ; let env3 = (env2 { runtime_env = rt_env })
     ; decMany dss env3}

      
tcEnv0 = unsafePerformIO(runFIO (decMany preDefDec initEnv) errF)
  where initEnv = TcEnv emptyFM toEnvX [] False 0 Z [] [] emptyFM emptyFM env0 [] initDI []
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

hasMonoType (var,(Forall (Nil ([],Rtau t)),_,_)) = return (var,t)
hasMonoType (var,x) = fail (show var++" does not have a monomorphic type")


toRep (TyCon "Bit" k) = Var (Global "Bit")
toRep (TyCon "Int" k) = Var (Global "Int")
toRep (TyCon "Z" k) = Var (Global "Z")
toRep (TyApp (TyCon "S" k) x) = App (Var (Global "S")) (toRep x)
toRep (TyApp (TyApp (TyCon "(,)" k) x) y) = 
  (App (App (Var (Global "Prod")) (toRep x)) (toRep y))
toRep (TyApp (TyApp (TyCon "Vec" k) x) y) = 
  (App (App (Var (Global "Vec")) (toRep x)) (toRep y))

appE [x] = x
appE (x:y:xs) = appE ((App x y):xs)

stringLit s = listExp (map (Lit . Char) s)
labelLit s = Lit(Tag s)

transForm (v,TyApp (TyCon "Exp" k) t) = return ("Exp1",v,toRep t)
transForm (v,TyApp (TyApp (TyApp (TyCon "Exp" k) c) row) t) = return ("Exp3",v,toRep t)
transForm (v,TyApp (TyCon "Sig" k) t) = return ("Sig1",v,toRep t)
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

--tcCircuit :: [Var] -> Exp -> [Dec] -> Expected Rho -> Mtc TcEnv Pred Exp
tcCircuit vs e ds expect = 
 do { allOk ds
    ; (_,frag,ds2) <- inferBndr localRename ds
    ; outputString ("\n\n"++show (Circ vs e ds)++"\n translates to \n")
    ; Frag env skols ts eqns rs <- zonk frag
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


instance Exhibit DispInfo Lit where
  exhibit d1 c = (d1,show c)
instance Exhibit DispInfo Exp where
  exhibit d1 c = (d1,show c)


instance Exhibit DispInfo Constr where
  exhibit d (Constr _ targs c doms Nothing) = 
    displays d [Ds "exists ",Dlf hf targs ",",Ds " . ",Ds (show c++" ")
               ,Dl doms ", "]
  exhibit d (Constr _ targs c doms (Just ps)) = 
    displays d [Ds "exists ",Dlf hf targs ",",Ds " . ",Ds (show c++" ")
               ,Dl doms ", ",Ds " where ",Dl ps ", "]

hf d (Global s,pt) = displays d [Ds ("("++show s++","), Dd pt, Ds ")"]
  
