-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Thu Mar  3 11:15:06 Pacific Standard Time 2005
-- Omega Interpreter: version 1.0

module Infer2 where

import Data.FiniteMap
import Monad(when,foldM)
import Monads
import Bind
import Syntax
import RankN
import List(partition,sort,sortBy,nub,union)
import Encoding2
import Auxillary(plist,plistf,Loc(..),report,foldrM,extend,extendL,backspace
                ,DispInfo(..),Display(..),initDI,dispL,disp2,disp3,disp4
                ,mergeDisp)
import LangEval(vals,env0)
import ParserDef(pCommand,parseString,Command(..),getExp)

pstr :: String -> TC ()
pstr = outputString

---------------------------------------------------------------------------
-- Set up the TC monad

localRename = False

type TC a = Mtc TcEnv Eqn a

inEnv :: TcEnv -> TC c -> TC c
inEnv env (Tc f) = Tc(\ x -> f env)
tcEnv :: TC TcEnv
tcEnv = (Tc (\ env -> return(env,[])))

instance TyCh (Mtc TcEnv Eqn) where
   envTvs = do { env <- getGenerics; foldrM f [] env }
      where f (name,typ) xs =
               do { vs <- get_tvs typ
                  ; if null vs then return xs
                               else return((show name,typ,vs):xs) }
   handleM = handleTC
   assume unifier m = 
        do { env <- tcEnv
           ; let env2 = env { assumptions = composeMGU unifier (assumptions env) }
           ; inEnv env2 m
           }
   getAssume = do { env <- tcEnv; return(assumptions env) }
   getDisplay = (Tc ( \ env -> return(displayInfo env,[])))
   normform x = do { --outputString ("Normalizing "++show x++"\n");
                     y <- zonk x
                   ; ans <- teval [] y
                   --; outputString ("To get: "++show ans++"\n")
                   ; return ans}

instance TracksLoc (Mtc TcEnv Eqn) where
  position = do { l <- getLoc; return l}
  failN dis loc n s = Tc h
    where h env = FIO(return(Fail dis loc n s))

-------------------------------------------------------------------------
-- The type checking environment TcEnv and its auxillary data types

-- type ToEnv = [(String,Tau,PolyKind)] -- In RankN.hs
data Frag = Frag [(Var,(Sigma,Level,Exp))] [TcTv] ToEnv [Eqn]

interesting (Frag env skols _ eqn) = not(null eqn)

nullFrag = Frag [] [] [] []

type Level = Int

-- The type of the internal environment of the Type Checking Monad
data TcEnv 
  = TcEnv { var_env :: FiniteMap Var (Sigma,Level,Exp) -- Term Vars
          , type_env :: [(String,Tau,PolyKind)] -- Type Vars
          , generics :: [(Var,Sigma)]    -- Lambda Bound Names
          , verbose :: Bool              -- Interactive Type Checking on?
          , level :: Int                 -- code level, counts brackets
          , location :: Loc              -- position in file
          , assumptions :: MGU           -- equality assumptions
          , runtime_env :: Ev            -- current value bindings
          , imports :: [(String,TcEnv)]  -- already imported Modules
          , displayInfo :: DispInfo      -- display info
          , tyfuns :: [(String,[Tau]-> TC Tau)] 
          }

tcEnv0 = TcEnv emptyFM toEnv0 [] False 0 Z [] env0 [] initDI []

----------------------------------------------------------
-- A class of data structures that are binding instances

class TypableBinder term where
  checkBndr :: Bool -> term -> Sigma -> TC(Frag,term)
  inferBndr :: Bool -> term -> TC(Sigma,Frag,term)

----------------------------------------------------------------
-- simple operations on Frag and TcEnv

-- One can perform substitution and zonking on Frags

instance TypeLike (Mtc TcEnv Eqn) Frag where
  sub env (Frag xs ys zs eqs) =
     do { xs' <- mapM f xs;
        ; eqs2 <- sub env eqs
        ; zs' <- mapM g zs
        ; return(Frag xs' ys zs' eqs2)}
    where f (v,(s,lev,exp)) = do { s2 <- sub env s; return(v,(s2,lev,exp))}
          g (str,tau,kind) =
            do { t2 <- sub env tau; k2 <- sub env kind; return(str,t2,k2)}
  zonk (Frag xs ys zs eqs) =
    do { xs2 <- mapM f1 xs; eqs2 <- mapM zonk eqs; return(Frag xs2 ys zs eqs2)}
   where f1 (x,(y,z,w)) = do { y' <- zonk y; return(x,(y',z,w))}
  get_tvs f = error "No way to get the type vars from a Frag"
  for_all f = error "No way to turn a Frag into a Sigma type"

infixr +++
(Frag xs ys zs eqs) +++ (Frag as bs cs eqs2) = Frag (xs++as) (ys++bs) (zs++cs) (eqs++eqs2)

getTyFuns :: TC [(String,[Tau]-> TC Tau)]
getTyFuns = Tc (\ env -> return (tyfuns env,[]))

addEqn :: [Eqn] -> Frag -> TC Frag
addEqn truths (Frag xs ys zs eqs) = return(Frag xs ys zs (truths++eqs))

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

collectEqn :: TC a -> TC (a,[Eqn])
collectEqn = extractAccum

--------------------------------------------------
-- Manipulating the environment part of the monad

letExtend :: MGU -> Frag -> TC a -> TC a
letExtend unifier (Frag pairs rigid tenv eqs) (Tc m) = Tc (\env -> m (extend env))
  where extend env = env { var_env = addListToFM (var_env env) pairs
                         , type_env = tenv ++ (type_env env)
                         , assumptions = composeMGU unifier (assumptions env) }

lambdaExtend :: MGU -> Frag -> TC a -> TC a
lambdaExtend unifier (Frag pairs rigid tenv eqs) (Tc m) = Tc (\env -> m (extend env))
  where g (x,(rho,lev,exp)) = (x,rho)
        extend env = env { var_env = addListToFM (var_env env) pairs
                         , generics = (generics env) ++ map g pairs
                         , assumptions = composeMGU unifier (assumptions env)
                         }

-- Run a computation under an extended environment that extends
-- only the facts in the environment
factExtend :: MGU -> TC a -> TC a
factExtend unifier (Tc m) = Tc (\env -> m (extend env))
  where extend env = env { assumptions = composeMGU unifier (assumptions env) }

underTypeEnv :: ToEnv -> TC a -> TC a
underTypeEnv new (Tc m) = Tc (\env -> m (extend env))
  where extend env = env { type_env = new ++ (type_env env) }


composeMGU :: MGU -> MGU -> MGU                         
composeMGU s1 s2 = ([(u,subTau s1 t) | (u,t) <- s2] ++ s1)

addFrag (Frag pairs rigid tenv eqs) env = extend env
  where extend env = env { var_env = addListToFM (var_env env) pairs
                         , type_env = tenv ++ (type_env env)
                         , assumptions = composeMGU unifier (assumptions env)}
        (Left unifier) = mgu (map f eqs)
        f (Equality x y) = (x,y)
        
addLetFrag (Frag pairs rigid tenv eqs) env =
    env { var_env = addListToFM (var_env env) pairs
        , assumptions = composeMGU unifier (assumptions env)}
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
                     Nothing -> failP 2 initDI ("Not in scope: "++show n)}

getVar :: Var -> TcEnv -> Maybe(Sigma,Level,Exp)
getVar nm env = lookupFM (var_env env) nm


-----------------------------------------------------------------
-- Types in syntax are stored asPT, we need to translate them
-- into Sigma types, and check that their well formed with Kind *
-- PT types stored in Data Decs are handled differently because they
-- may have kinds other than *, and they are not always generalized.

checkPT :: PT -> TC Sigma
checkPT pt = do { tenv <- getTypeEnv
                ; let name (nm,tau,kind) = nm
                      g nm = do { kind <- newKind star1
                                ; var <- newFlexiTyVar kind
                                ; return(nm,TcTv var,poly kind)}
                ; freeEnv <- mapM g (getFree (map name tenv) pt)
                ; s <- toSigma (freeEnv ++ tenv) pt
                ; check s (Star 0)
                ; s2 <- generalize s
                ; return s2}

-- In a type synonym like:
-- type ListInt = [ Int ]
-- the type must be well kinded in the current environment

inferPT :: PT -> TC(Tau,PolyKind)
inferPT pt = 
  do { tenv <- getTypeEnv
     ; s <- toTau tenv pt
     ; (k::Tau,ty) <- infer s
     ; return(ty,K(Forall (Nil([],Rtau k))))
     }

--------------------------------------------------------------------
-- Literals are Typable

instance Typable (Mtc TcEnv Eqn) Lit Rho where
  tc x@(Int n) expect = zap x (Rtau intT) expect
  tc x@(Char c) expect = zap x (Rtau charT) expect
  tc x@(Unit) expect = zap x (Rtau unitT) expect
  tc x@(ChrSeq s) expect = zap x (Rtau chrSeqT) expect
  tc x@(Symbol n) expect = zap x (Rtau symbolT) expect
  tc x@(Float n) expect = zap x (Rtau floatT) expect

--------------------------------------------------------------------
-- Functions to report reasonably readable  errors

notfun e fun_ty dis s =
   failP 2 dis ("\nIn the expression: "++show e++
                   "\nthe function has a non-functional type: "++
                   show fun_ty)

badarg e arg_ty dis s = do { z <- zonk arg_ty;
   failP 2 dis ("\nIn the expression: "++show e++
            "\nthe argument did not have type: "++pprint arg_ty++"\n"++s)}

resulterr e res_ty expect dispInfo s =
  do { ex <- case expect of {Check t -> return t; Infer ref -> readRef ref }
     ; rt <- zonk res_ty
     ; ex2 <- zonk ex
     ; info <- getDisplay
     ; info1 <- return(mergeDisp dispInfo info)
     ; let (info2,a) = disp info1 rt
           (info3,b) = disp info2 ex
     ; failP 2 info3 ("\nIn the expression: "++show e++"\nthe result type: "++
                a++"\nwas not what was expected: "++b++"\n"++s
                ++show rt++","++show ex2
                )}

morePoly::(Show a,Show b,Show c,Display b,Display c,Subsumption m b(Expected c),TypeLike m b,TypeLike m c)
          => a -> b -> Expected c -> m ()
morePoly exp sigma expect =
   handleM 2 (morepoly sigma expect) (resulterr exp sigma expect)


--------------------------------------------------------------------
-- This instance is useful for a first class pattern decl like:
-- pattern LHS = RHS
-- pattern If x y z = Case x [(True,y),(False z)]
-- where we need to check that the pattern on the RHS is well formed
-- when using the variables defined on the LHS.

instance Typable (Mtc TcEnv Eqn) Pat Rho where
  tc (Plit l) expect = do { l2 <- tc l expect; return(Plit l2) }
  tc (Pvar v) expect =
     do { (sigma,n,Var u) <- lookupVar v
        ; morePoly (Pvar v) sigma expect
        ; return(Pvar u)}

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
  tc p expect = failP 2 initDI ("Bad pattern on RHS of pattern decl: "++show p)


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
        ; return(Frag [(var,(t,level,Var v))] [] [] [],v) }
  inferBndr rename var =
     do { sigma <- newSigma star;
        ; level <- getLevel
        ; v <- alphaN rename var
        ; return(sigma,Frag [(var,(sigma,level,Var v))] [] [] [],v) }


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
          ; ((t1,t2),truths) <- collectEqn (sigmaPair t2)
          ; a1 <- zonk t1; a2 <- zonk t2
          --; outputString ("After sigmaPair" ++ show a1++ " | "++show a2)
          ; (frag1@(Frag _ _ _ eqs),p1) <- checkBndr rename x t1
          -- Facts generated in the first part of a tuple can be used to check the second
          ; unifier <- handleM 3 (mguM eqs) (mErr eqs x t1)
          
          ; (frag2,p2) <- factExtend unifier (checkBndr rename y t2)
          ; tZ <- zonk t
          ; frag3 <- addEqn truths (frag1+++frag2)
          ; return(frag3,Pprod p1 p2)}
     ch (Psum inj p) =
       do { ((t1,t2),truths) <- collectEqn (sigmaSum t)
          ; (frag1,p1) <- checkBndr rename p (case inj of {L -> t1; R -> t2})
          ; frag2 <- addEqn truths frag1
          ; return(frag2,Psum inj p1)}
     ch (Paspat v p) =
       do { (frag1,p1) <- checkBndr rename p t
          ; (frag2,u) <- checkBndr rename v t
          ; return(frag1+++frag2,Paspat u p1) }
     ch Pwild = return(nullFrag,Pwild)
     ch (Pcon c ps) =
       do { (sigma,n,exp) <- lookupVar c
          --; pstr ("In checkBndr t ="++show t++" sigma = "++show sigma)
          ; loc <- getLoc
          ; current <- getAssume
          --; outputString ("\n1 %% "++show c++" current = "++ show current++show sigma)
          ; (rigid,assump,rho) <- instanPatConstr Ex loc (show p) sigma
          ; range <- constrRange ps rho
          --; pstr ("range = "++show range++" t = "++show t++" assump = "++show assump)
          ; (_,truths) <- collectEqn (morepoly t range)
          ; ass <- zonk assump -- After the morepoly check we need to zonk
          ; r1 <- zonk rho
          ; t1 <- zonk t
          --; outputString ("2 %% "++show c++" assump = "++show assump++" ass = "++show ass)
          --; outputString ("3 %% "++show ass++show r1++" should have type "++show t)
          ; (frag,ps',result) <- checkBndrs rename ps r1
          ; frag3 <- addEqn truths (frag+++(Frag [] rigid [] ass))
          ; return(frag3,Pcon c ps')}
     ch (Pann p ty) =
       do { sigma <- checkPT ty
          ; (_,truths) <- collectEqn (morepoly t sigma)
          ; (frag,p') <- checkBndr rename p t
          ; frag2 <- addEqn truths frag
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
          ; return(Forall (Nil (assump2,result)),frag+++(Frag [] rigid [] assump),Pcon c ps')}
    inf pat@(Pann p ty) =
       do { sigma <- checkPT ty
          ; (frag,p') <- checkBndr rename p sigma
          ; return(sigma,frag,Pann p' ty)}


-----------------------------------------------------------------------

inferBndrs :: Bool -> [Pat] -> TC([Sigma],Frag,[Pat])
inferBndrs rename ps =
    do { ws <- mapM (inferBndr rename) ps; return(foldr acc ([],nullFrag,[]) ws)}
  where acc (r,frag1,p) (rs,frag2,ps) = (r:rs,frag1+++frag2,p:ps)


checkBndrs :: Bool -> [Pat] -> Rho -> TC(Frag,[Pat],Rho)
checkBndrs rename [] result_ty = return(nullFrag,[],result_ty)
checkBndrs rename (p:ps) rho =
  do { (dom,rng) <- unifyFun rho
     --; pstr ("\n*** "++show p++" :: "++show rho++"\nwith "++show dom++" -> "++show rng)
     ; (frag1@(Frag _ _ _ eqs),p1) <- handleM 2 (checkBndr rename p dom) (pErr p ps dom)
     -- Facts generated in earlier patterns can be used to check later patterns
     ; unifier <- handleM 3 (mguM eqs) (mErr eqs p dom)
     ; (frag2,ps1,result_ty) <- factExtend unifier (checkBndrs rename ps rng)
     ; return(frag1+++frag2,p1:ps1,result_ty) }


pErr p moreps dom d1 mess = 
  failP 2 d3 ("While checking that the pattern: "++pS++" : "++domS++"\n"++mess++postScript)
 where (d2,pS,domS) = disp2 d1 (p,dom)
       (d3,morepsS) = dispL disp d2 moreps "," 
       postScript = "\n(if this is a solving problem, perhaps the pattern might swap places "++
                    "\nwith one of the other patterns "++ morepsS++" which might establish the facts"++ 
                    "\nto prove the condition. Recall, facts accumulate from left to right.)"         

mErr eqs p dom d1 mess =
  failP 2 d2 ("While checking that the pattern "++pS++" : "++domS++"\n"++ mess)
 where (d2,pS,domS) = disp2 d1 (p,dom)
        
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
     ; tmap2 <- mapM genTyCon tmap
     ; let f (nm,tau,polykind) = (nm,tau)
     ; cmap2 <- genConstrFunFrag (map f tmap2) cmap
     ; let liftToTypeEnv (Global s,(sig,n,exp)) = (s,TyCon s (K sig),K sig)
           (types,values) = 
             if strata == typeStrata
                then (tmap2,cmap2)
                else (map liftToTypeEnv cmap2 ++ tmap2,[])
                 
     ; return(simpleSigma unitT,Frag values [] types [],ds)
     }

-- translate a [Eqn] from a Maybe[(PT,PT)]           
toEqn env Nothing = return[]
toEqn env (Just xs) = mapM f xs
  where f (x,y) = do { a <- toTau env x; b <- toTau env y; return(Equality a b) }

doManyData strata ds = 
  do { envMap <- getTypeEnv
     ; let proj (x,y,z) = (x,y)
     ; info <- mapM (dataBinds strata envMap) ds
     ; let acc (t,c) (ts,cs) = (t:ts,c++cs)
           (tMap,constrBinds) = foldr acc ([],[]) info
     ; let g (loc,name,allExParams,env2,eqs,body) = 
             do { let env3 = env2 ++ tMap
                ; eqs2 <- toEqn env3 eqs
                ; body2 <- toRho env3 body
                ; let typ = Forall (windup allExParams (eqs2,body2))
                --; outputString (show strata ++ " Check "++name++" :: "++pprint typ)
                ; newLoc loc $ hasKind name typ (MK (Star strata))
                ; return(Global name,(typ,0::Level,Var(Global name)))
                }
     ; cMap <- mapM g constrBinds
     ; return (tMap,cMap)
     }

    
-- compute typings and kindings from a Dec, they'll be checked later in "doManyData"

dataBinds:: Strata -> (ToEnv) -> Dec -> TC((String,Tau,PolyKind),[ConType])
dataBinds strata currentEnv (Data loc _ (t@(Global tname)) sig xs cs derivs) = 
  do { let (allArgs,eqs,hint) = sigToForallParts strata sig
     ; if null eqs then return () else failP 2 initDI ("data signature cannot have equations: "++showPairs eqs)
     ; (allParams,allEnv) <- argsToEnv allArgs currentEnv
     ; (argBinds,rng) <- newLoc loc (useSigToKindArgs strata xs hint)
     ; (argParams,argEnv) <- argsToEnv argBinds allEnv
     ; let tkindbody = foldr Karrow' rng (map (\(nm,pt,q)->pt) argBinds)
           tType = TyCon' tname
           var (s,k,q) = TyVar' s
           rngType = applyT' (tType : map var argBinds) 
     ; cTypes <- mapM (conType strata (allParams ++argParams) argEnv rngType) cs
     --; outputString ("AllEnv = " ++ show allEnv++"\ntkindbody = "++show tkindbody)
     ; rho <- toRho allEnv tkindbody
     ; tkind <- return (K(Forall(windup allParams ([],rho))))
     ; return((tname,TyCon tname tkind,tkind),cTypes) }


type ConType = (Loc,String,ForAllArgs,ToEnv, Maybe[(PT,PT)],PT)

conType :: Strata -> ForAllArgs -> (ToEnv) -> PT -> Constr -> TC ConType
conType strata allParams allEnv rng (Constr loc exs c@(Global cname) ts eqs) = 
    do { (exParams,allExEnv) <- argsToEnv (map f exs) allEnv
       ; return(loc,cname,allParams ++ exParams,allExEnv,eqs,cbody) }
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
sigToForallParts strata (Just (Forallx binds eqs t)) = (binds,eqs,Just t)
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
  walk [] (Just t) = failP 2 initDI ("Explict kinding for new type must result in kind *0, not "++show t)
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
       else failP 2 initDI ("data Dec has explicit signature and explicit kindings on arguments, "++
                            "but they don't match. "++
                            show d1++" /= "++show d2)
  walk (v:vs) (Just t) = failP 2 initDI ("Expecting kind arrow like (a ~> b), found: "++show t)


genConstrFunFrag tyConSub xs = mapM f xs where
  f (nm,(sig,lev,exp)) =
    do { -- Replace TyCon's which have stale (i.e. mono) PolyKind fields
         sig1 <- sub ([],[],tyConSub) sig
       ; sig2 <- generalize sig1  -- Now generalize
       ; return(nm,(sig2,lev,exp))}

genTyCon :: (String,Tau,PolyKind) -> TC (String,Tau,PolyKind)
genTyCon (nm,TyCon _ _,K k) =
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

displayFragElem  (nm,(sig,lev,exp)) = outputString (show nm++" : "++alpha [] sig++"\n")


instance TypableBinder [Dec] where
  inferBndr renm [] = return(simpleSigma unitT,nullFrag,[])
  inferBndr renm ds | all isData ds= checkDataDecs typeStrata(useTypeSig ds)
  inferBndr renm ds | all isKind ds= checkDataDecs kindStrata(useTypeSig ds)
  inferBndr renm ds | all isValFunPat ds =
    do { let decs = useTypeSig ds
       ; (frag@(Frag xs _ _ _),triples) <- getDecTyp renm decs -- Step 1
       --; (mapM_ displayFragElem xs)
       --; outputString(show triples)
       ; ds2 <- mapM (checkDec frag) triples -- Step 2
       ; frag2@(Frag xs zs tenv eqs) <- genFrag frag
       --; when (not renm) (mapM_ displayFragElem xs)
       ; return(simpleSigma unitT,frag2,ds2)
       }
  inferBndr rename ds = failP 2 initDI ("\nMixup in Decs\n"++show ds)
  checkBndr rename ds = error "Can't checkBndr a [Dec]"

-- Step 1. Compute just the "frag" for the decls. Don't do their bodies yet.

getDecTyp :: Bool -> [Dec] -> TC (Frag,[(Rho,Dec,[Eqn])])
getDecTyp rename [] = return(nullFrag,[])
getDecTyp rename (d:ds) =
  do { (frag1,rho,d,eqns) <- getOneDec rename d
     ; (frag2,triples) <- getDecTyp rename ds
     ; return(frag1 +++ frag2,(rho,d,eqns):triples) }

getOneDec rename (Val loc pat body ds) = newLoc loc $
  do { (sigma,frag,pat2) <- inferBndr rename pat
     ; (rigid,assump,rho) <- rigidTy Ex loc (show pat) sigma
     --; outputString ("\ngetOneDec pat = "++show pat++" sigma = "++show sigma++
     --                " rho = "++show rho++"\n rigid = "++show rigid)
     ; return(frag,rho,Val loc pat2 body ds,assump)}
getOneDec rename (Fun loc nm hint ms) = newLoc loc $
  do { sigma <- case hint of { Just ty -> checkPT ty
                             ; Nothing -> newSigma star}
     ; (frag,nm2) <- checkBndr rename nm sigma
     ; (rigid,assump,rho) <- rigidTy Ex loc (show nm) sigma
     ; r1 <- zonk rho
     --; outputString("In getOneDec \n"++show nm++" :: "++show sigma++" expected type "++show r1)
     ; return(frag,rho,Fun loc nm2 hint ms,assump)}
getOneDec rename (Pat loc nm vs p) = newLoc loc $
  do { (sigma,frag,nm2) <- inferBndr rename nm
     ; (rigid,assump,rho) <- rigidTy Ex loc (show nm) sigma
     ; return(frag,rho,Pat loc nm2 vs p,assump)}
getOneDec rename (Reject s ds) = return (nullFrag,Rtau unitT,Reject s ds,[])
getOneDec rename (Prim l nm t) =
  do { (sigma,frag,_) <- inferBndr rename (Pann (Pvar nm) t)
     ; return(frag,error "Shouldn't Check Prim type",Prim l nm t,[]) }
getOneDec rename d = failP 2 initDI ("Illegal dec in value binding group: "++show d)

-- rigidTy is called when checking the body of a Dec with an explicit
-- type signature. It replaces all type variables with kinds classified
-- by *1 (i.e. *0 or other kinds classified by *1) with
-- new rigid type variables. For example a type like
-- (forall (k:*1) (u:k) a . (AtomX u) -> a -> Pair)
-- should rigidify "u" and "a", but not "k"

rigidTy :: TyCh m => Quant -> Loc -> String -> Sigma -> m([TcTv],[Eqn],Rho)
rigidTy q loc s sigma = unBindWith new sigma
   where new nam quant (k@(MK(Star 0))) = 
             do { v <- newRigidTyVar q loc s k; return(TcTv v)}
         new nam quant (k@(MK (TyVar _ (MK (Star 1))))) = 
             do { v <- newRigidTyVar q loc s k; return(TcTv v)}
         new nam quant (k@(MK (TcTv (Tv unq flav (MK (Star 1)))))) = 
             do { v <- newRigidTyVar q loc s k; return(TcTv v)}             
         new nam quant (k@(MK(TyCon _ (K (Forall (Nil (_,Rtau (Star 1)))))))) = 
             do { v <- newRigidTyVar q loc s k; return(TcTv v)}
         new nam quant k = 
             do { v <- newRigidTyVar q loc s k; return(TcTv v)}
         new nam quant k = do { v <- newFlexiTyVar k; return(TcTv v) }
       


-- Step 2. Compute the bodies. All the names being bound are 
-- already in the frag passed as input.

checkDec frag (rho,Val loc pat body ds,eqns) = newLoc loc $
  do { (_,frag2,ds2) <- inferBndr localRename ds
     ; unifier <- fragMGU ("Checking where clause of "++show pat) frag2
     ; frag3 <- addEqn eqns frag 
     --; outputString ("\npat = "++show pat++" rho = "++show rho)
     --; showFrag "\nWith equations = " frag3
     ; body2 <- underLet ("CheckDec "++show pat) 
                         frag3
                         (lambdaExtend unifier frag2 (check body rho))
     ; return(Val loc pat body2 ds2) }
checkDec frag (rho,Fun loc nm hint ms,eqns) = newLoc loc $
  do { frag3 <- addEqn eqns frag
     ; let chMs [] rho = return []
           chMs (m:ms) rho =
              do { m1 <- underLam frag3 ("CheckDec "++show nm) (check m rho)
                 ; m1s <- chMs ms rho; return(m1:m1s)}
     ; (ms2,zs) <- collectEqn (chMs ms rho)
     ; when (not (null zs)) (failP 3 initDI ("Undischarged obligations: "++showEqn zs))
     ; return(Fun loc nm hint ms2) }
checkDec frag (rho,Pat loc nm vs p,eqns) = newLoc loc $
  do { frag3 <- addEqn eqns frag 
     ; unifier <- fragMGU ("Checking "++show nm) frag3
     ; (Forall (Nil (assump,ty)),(Frag xs tvs tenv eqs),p2)
               <- lambdaExtend unifier frag3 (inferBndr False p)
     ; argtys <- compareL vs xs
     ; morepoly (foldr arrow ty argtys) rho
     ; return(Pat loc nm vs p2)
     }
checkDec frag (rho,Reject s ds,eqns) =
  handleM 7 (do { (_,frag2,ds2) <- inferBndr localRename ds
                ; error ("\nReject test: "++s++" did not fail.")}) errF
 where errF dis _= do { outputString ("\n*** negative test '"++ s ++ 
                                  "' fails as expected\n")
                  ; return (TypeSig Z (Global "##test") tunit')}
checkDec frag (_,Prim loc nm t,eqns) = newLoc loc $ return(Prim loc nm t)
checkDec frag d = failP 2 initDI ("Illegal dec in value binding group: "++show d)

----------------
-- Helper functions for typing [Dec]

-- Generalize a Frag after type inference

genFrag (Frag xs ys tenv eqs) = 
     do { zs <- mapM gen xs; return(Frag zs ys tenv eqs)}
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
              (failP 2 initDI ("Unknown var in pattern: "))
       ; return tys }
  where get x = case lookup x fs of
                  Nothing -> failP 2 initDI ("Unused formal parameter: "++show x)
                  Just (ty,_,_) -> return ty

-- Generate a reasonable error message when Skolem vars escape

instance Display String where
  disp d s = (d,s)

escapes :: TyCh m => [(String,Sigma,[TcTv])] -> [TcTv] -> m ()
escapes trips [] = return ()
escapes trips bad = do { as <- getAssume
                       ; (display,lines) <- foldrM (f as) (initDI,"") bad
                       ; failP 2 display lines }
  where f as (Tv _ (Rigid All loc s) k) (d1,str) = return $
           (d1,"At "++show loc++" the explict typing: "++s++
            " is not polymorphic enough."++str)
        f as (v@(Tv _ (Rigid Ex loc s) k)) (d1,str) =
          do { (d2,var) <- get d1 v trips
             ; let (d3,v1,var1) = disp2 d2 (v,var)
             ; return(d3,"\nAn existential type var: "++v1++
                         "\narising from the pattern: "++s++" at "++show loc++
                         "\nescapes into the environment in the type of "++var) }
        get display v [] = return (display,"")
        get display v ((name,typ,vs):xs) =
            do { t <- zonk typ
               ; if v `elem` vs
                    then let (d2,t2) = disp display t
                         in return(d2,name++" : "++t2) 
                    else get display v xs }

escapeCheck :: (TyCh m,Show a) => a -> Rho -> Frag -> m ()
escapeCheck term typ (Frag _ skolvars _ _) = 
 do { resultVars <- get_tvs typ
    ; let bad = filter (`elem` resultVars) skolvars
    ; when (not (null bad)) 
           (escapes [("the exp\n   "++show term,(Forall (Nil([],typ))),bad)] bad)
    }

-----------------------------------------------------------------

fragMGU :: String -> Frag -> TC MGU
fragMGU info (Frag _ _ _ eqs) = handleM 3 (mguM eqs) err
  where err d1 mess = failP 2 d2 ("Couldn't build unifier for: "++unif++
                                  " because "++info++" "++mess)
          where (d2,unif) = disp d1 eqs                        
 

underLam :: Frag -> String -> TC a -> TC a
underLam frag p x =  do { unifier <- fragMGU p frag
                        ; under (lambdaExtend unifier) p frag x
                        }
                      
underLet :: String -> Frag -> TC a -> TC a
underLet s frag x = 
  do { unifier <- fragMGU s frag
     ; under (letExtend unifier) s frag x
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


-- HERE ### 
under :: (Frag -> b -> TC c) -> String -> Frag -> b -> TC c
under extend p frag@(Frag xs patVars tenv eqs) comp =
  do { eqs1 <- zonk eqs
     ; assumptions <- return ([]::[Eqn]) -- getAssume
     ; when (prefix "DEBUG" p) $ outputString ("\nEnter Under "++p++"\nFrag Eqns = "++showEqn eqs1++"\nAssump Eqns = "++showEqn assumptions);
       (a,need) <- handleM 3 (collectEqn(extend frag comp)) (underErr1 patVars)
     ; when (prefix "DEBUG" p) $ outputString (p++" Computed Need = "++showEqn need++ " patVars = "++show patVars)
     ; (_,residual) <- handleM 1 (collectEqn  (solve2 need)) -- (solve True p (eqs2++assumptions) need))
                       (underErr frag p (assumptions) need)
     ; (unsolved,passOn) <- splitObligations residual patVars
     ; when (not (null unsolved)) (failP 2 initDI ("Unresolved obligations: "++showEqn unsolved))

     ; triples <- envTvs
     ; let envVars = varsFromTriples triples 
     ; let bad = filter (`elem` envVars) patVars
     ; when (not (null bad)) (escapes triples bad)
     ; injectAccum passOn
     ; return a
     }



underErr frag pat assump oblig info s = showFrag "UnderErr" frag >> failP 2 info2 message
  where (info2,a,o) = disp2 info (assump,oblig)
        message = "\nWhile type checking in the scope of\n   "++pat++
                  "\nWe need to prove\n   "++o++
                  "\nFrom the assumptions\n   "++a++
                  "\nBut "++s
        

splitObligations :: [Eqn] -> [TcTv] -> TC([Eqn],[Eqn])
splitObligations need patVars = do { xs <- mapM f need; return(split xs ([],[])) }
  where f x = do { vs <- get_tvs x; return (x,vs) }
        split [] pair = pair
        split ((x,vs):xs) (yes,no) =
           split xs (if any (`elem` patVars) vs then (x:yes,no) else (yes,x:no))

--------------------------------------------------------------------------

peek :: TC a -> TC (a,[Eqn])
peek x = do { (a,eqs) <- collectEqn x; injectAccum eqs; return(a,eqs) }

instance Typable (Mtc TcEnv Eqn) (Body Exp) Rho where
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

instance Typable (Mtc TcEnv Eqn) (Match [Pat] Exp Dec) Rho where
  tc (loc,ps,body,ds) (Check t) = newLoc loc $
     do { (frag1,ps1,rng) <- checkBndrs localRename ps t
        ; t11 <- zonk t
        ; when False -- (interesting frag1)
           (showFrag ("\nIn Fun Match, t = "++show t11++"\nps = "++show ps++"\n") frag1)
        ; let err dis s  =
               (do { (Frag zs _ _ ts) <- zonk frag1
                   ; truths <- getAssume
                   ; let (i2,tstring) = disp dis t
                         (i3,zsString) = disp i2 zs
                         (i4,truthString) = disp i3 (subEqn truths ts)
                   ; failP 3 i4
                      (("\n*** Error in clause: "++plist "" ps " " " = ")++
                               (show body++ " :\n    " ++ tstring {- show t -} )++
                       ("\n*** with\n   "++zsString)++ -- plistf showBind "" zs "\n          " "")++
                       ("\n*** where "++ truthString {- showEqn (truths++ts) -} )++
                       s)
                   } )

        ; (_,frag2,ds2) <- underLam frag1 ("fun "++(show ps)) 
                                   (inferBndr localRename ds)
        ; body3 <- handleM 2 (underLet "Y" frag2
                                       (underLam frag1 (show ps) 
                                                 (checkTest body rng))) err
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

checkTest body rng =
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

instance Typable (Mtc TcEnv Eqn) (Match Pat Exp Dec) Rho where
  tc (loc,p,body,ds) (Check t) = newLoc loc $
     do { ((dom,rng),obs) <- collectEqn (unifyFun t)
        --; outputString ("After unifyFun "++show dom++" -> "++show rng)
        ; (frag1,p1) <- checkBndr localRename p dom
        --; outputString ("Frag = ")
        ; let err dis s  =
	       (do { (Frag zs _ _ ts) <- zonk frag1
	           ; truths <- getAssume
	           ; failP 2 dis
	                (("\n*** Error in clause: "++show p++" -> "++show body++ "  :  " ++ show t)++
	                 ("\n*** with  "++plistf showBind "" zs "\n          " "")++
	                 ("\n*** where "++showEqn (subEqn truths ts))++ s) } )
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

instance Typable (Mtc TcEnv Eqn) Exp Rho where
  tc (Lit x) expect = do { x' <- tc x expect; return (Lit x') }
  tc (Var v) expect =
     do { m <- getLevel
        --; when (show v=="h") (outputString ("Checking variable "++show v))
        ; (sigma,n,exp) <- lookupVar v
        ; when (n > m) (failP 2 initDI (show v++" used at level "++show m++" but defined at level "++show n))
        --; when (show v=="h") $ outputString ("Sigma = "++show sigma++" Expect = "++show expect)
        ; morePoly (Var v) sigma expect
        --; when (show v=="h") $ outputString ("Poly check succeeds"++show sigma)
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
     do { ann_ty <- checkPT pt
        ; exp <- check body ann_ty
        ; morePoly term ann_ty exp_ty
        ; return (Ann exp pt) }
  tc (Let ds e) expect =
     do { (_,frag,ds2) <- inferBndr localRename ds
        ; e2 <- underLet "LetExp" frag (tc e expect)
        ; return(Let ds2 e2)}
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
        ; ts <- getAssume
        ; truths <- zonk ts
        ; typ <- zonk ty
        ; let (eD) = show e
              (d2,typD) = disp initDI typ
              (d3,eqnD) = disp d2 truths
        ; outputString ("\n*** Checking: " ++ eD ++
                   "\n*** has type: " ++ typD ++
                   "\n***    Where: " ++ eqnD)
        ; env <- tcEnv
        ; checkLoop typ d3 env
        ; x <- tc e expect 
        ; return(CheckT x)}
  tc (Lazy e) expect = do { x <- tc e expect; return(Lazy x)}
  tc (Under e1 e2) expect = error "Under"
  tc (Bracket exp) expect =
     do { a <- unifyCode expect
        ; e <- levelInc (check exp a)
        ; return(Bracket e)}
  tc (Escape exp) expect =
     do { n <- getLevel
        ; case (n,expect) of
           (0,_) -> failP 2 initDI ("Esc at level 0: "++show (Escape exp))
           (_,Check t) ->
              do { e <- levelDec(check exp (tcode t)); return(Escape e)}
           (_,Infer ref) ->
              do { t <- newRho star
                 ; e <- levelDec (check exp (tcode t))
                 ; writeRef ref t
                 ; return(Escape e) }}
  tc (Run exp) (Check t) =
      do { e <- levelDec(check exp (tcode t)); return(Escape e)}
  tc (Run exp) (Infer ref) =
      do { t <- newRho star
         ; e <- levelDec (check exp (tcode t))
         ; writeRef ref t
         ; return(Escape e) }
  tc (Reify s v) expect = error ("Unexpected reified value: "++s)


tcStmts m b [] = failP 2 initDI "Do should have at least one statement"
tcStmts m b [NoBindSt loc e] =
   do { e2 <- newLoc loc (check e (Rtau (TyApp m b)))
      ; return([NoBindSt loc e2])}
tcStmts m b [st@(BindSt loc pat e)] =
   failP 2 initDI ("Last stmt in Do must not be a bind: "++show st)
tcStmts m b [st@(LetSt loc ds)] =
   failP 2 initDI ("Last stmt in Do must not be Let: "++show st)
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
    (a@(Forallx xs _ x),b@(Forallx ys _ y)) ->
        do { t1 <- checkPT a
           ; t2 <- checkPT b
           ; b <- morepoly t1 t2; outputString (show b ++ "\n") }
    (a@(Forallx xs _ x),y) ->
        do { t1 <- checkPT a
           ; t2 <- toRho toEnv0 y
           ; b <- morepoly t1 t2; outputString (show b ++ "\n") }
    (x,y) ->
        do { t1 <- toRho toEnv0 x
           ; t2 <- toRho toEnv0 y
           ; b <- morepoly t1 t2; outputString (show b ++ "\n") }) :: TC ())


----------------------------------------------------------------------------
-- when we have a [Dec] some of these Decs might be type signature like:
-- f :: a -> b -> M c
-- We want to take these and "push them down" onto the other Dec in the list.
-- This is done by placing them as annotations in Pat decls, and as optional
-- "hints" in Fun decls, data decls, and type-fun decls

pushHints [] d = d
pushHints protos (Fun loc nm _ ms) = Fun loc nm (applyName protos nm) ms
pushHints protos (Data loc n nm sig vs cs ders) = Data loc n nm (applyName protos nm) vs cs ders
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


frag0 = Frag (map f vals) [] [] []
  where f (nm,(v,sigma)) = (Global nm,(sigma,0,Var (Global nm)))

initTcEnv = addFrag frag0 tcEnv0


-- A version in the FIO monad that returns unresolved NEED as well
-- as the final TcEnv and the transformed Decs

checkDecs :: TcEnv -> [Dec] -> FIO (TcEnv,[Dec],[Eqn])
checkDecs env ds = do { ((a,b),c) <- unTc (checkBndGroup ds) env; return(b,a,c)}

checkBndGroup :: [Dec] -> TC([Dec],TcEnv)
checkBndGroup [d@(TypeSyn loc nm pt)] = 
  do { env <- tcEnv
     ; (tau,kind) <- inferPT pt
     ; return([d],env{type_env = (nm,tau,kind):(type_env env)})
     }
checkBndGroup ds | all isTypeFun ds = 
  do { let ds2 = useTypeSig ds   -- push the signatures inside the TypeFun definitions 
     ; env <- tcEnv
     ; env2 <- computeTypeFunEnv env ds2
     ; pairs <- checkTypeFuns env2 ds2
     ; let env4 = env2{tyfuns = pairs ++ tyfuns env2}
     ; return(ds2,env4)}
checkBndGroup ds =
  do { (sigma,frag,ds2) <- inferBndr False ds
     ; unifier <- fragMGU "Checking declaration group" frag
     ; env <- letExtend unifier frag tcEnv
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
          do { (nmType,nmTypeKind) <- inferPT pt
             ; let poly = K(simpleSigma nmType)
             ; return (nm,TyCon (nm) poly,poly) }

checkTypeFuns :: TcEnv -> [Dec] -> TC [(String,[Tau] -> TC Tau)]
checkTypeFuns env [] = return []
checkTypeFuns env1 (TypeFun loc nm (Just pt) ms : more) = 
  do { (nmType,nmTypeKind) <- inferPT pt
     ; let poly = K(simpleSigma nmType)
           down (Karr x y) xs = down y (xs++[x])
           down rng xs = (rng,xs)
           (rng,ks) = down nmType []
     ; clauses <- mapM (checkLhsMatch (type_env env1) ks rng) ms
     ; morepairs <- checkTypeFuns env1 more
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
tmatch x y env = Nothing     

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
teval env x = return x         
      
-- check the lhs (i.e. {plus (S x) y} = ... ) of each match

checkLhsMatch :: ToEnv -> [Tau] -> Tau -> ([PT],PT) -> TC ([Tpat],Tau)
checkLhsMatch current ks range (ps,rhs) = 
  do { (_,pats) <- thrd [] toTpat (tail ps)   -- ps = {plus (S x) y} throw away "plus"
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

instance Show Tpat where
  show (Tvar s nm) = s -- ++"("++show nm++")"
  show (Tcon s []) = s
  show (Tcon s xs) = "(" ++ s ++ plist " " xs " " ")"
  show (Tfun s xs) = "{" ++ s ++ plist " " xs " " "}"
  show (Tstar 0) = "*"
  show (Tstar n) = "*"++show n
  show (Tkarr a b) = "("++show a++" ~> "++show b++")"

-- Translate a PT (the type that is parsed) into a Tpat. This is relatively
-- straightforward, the only difficult part is that every type application
-- must start with a TyCon, or it won't be a legitimate type-pattern
-- and that duplicate names (i.e. a var that appears twice in a pattern) 
-- must map to the same Tvar for every occurrence.
  
toTpat :: HasNext m => PT -> [(String,Tpat)] -> m ([(String,Tpat)],Tpat)
toTpat (TyVar' s) env = 
  case lookup s env of
    Nothing -> do { nm <- fresh; let u = Tvar s nm in return((s,u):env,u)}
    Just v -> return(env,v)
toTpat (x@(TyApp' _ _)) e1 =
  do { let down (TyApp' (TyCon' s) x) = return(s,[x])
           down (TyApp' x y) = do { (c,ys) <- down x; return(c,ys++[y])}
           down y = fail ("Root of ("++show x++") is not a type constructor: "++show y)
     ; (constr,args) <- down x
     ; (e2,params) <- thrd e1 toTpat args
     ; return(e2,Tcon constr params)}
toTpat (Rarrow' x y) e1 = 
  do { (e2,dom) <- toTpat x e1
     ; (e3,rng) <- toTpat y e2
     ; return(e3,Tcon "(->)" [dom,rng])}
toTpat (Karrow' x y) e1 = 
  do { (e2,dom) <- toTpat x e1
     ; (e3,rng) <- toTpat y e2
     ; return(e3,Tkarr dom rng)}
toTpat (TyCon' s) e1 = return(e1,Tcon s [])
toTpat (Star' n) e1 = return(e1,Tstar n)
toTpat (TyFun' (TyVar' s : xs)) e1 = 
  do { (e2,ys) <- thrd e1 toTpat xs
     ; return(e2,Tfun s ys) }
toTpat x e1 = fail ("The type: "++show x++" is not appropriate for the LHS of a type fun.")

thrd e1 f [] = return(e1,[])
thrd e1 f (x:xs) = do { (e2,y) <- f x e1; (e3,ys) <- thrd e2 f xs; return(e3,y:ys)}

getInfo y [] s = fail ("While checking the lhs: "++show y++" unknown type: "++s)
getInfo y ((x,tau,k):xs) s = if s==x then return (tau,k) else getInfo y xs s
 
-- In order to kind-check a type function we need to compute that the 
-- given kind is consistent with the LHS of each clause, and we also
-- need to build a ToEnv, so that we can correctly parse the RHS

checkPTBndr :: ToEnv -> (Tpat,Tau) ->  TC ToEnv
checkPTBndr current (Tvar s nm,k) =
  return[(s,TyVar nm (MK k),poly (MK k))]
checkPTBndr current (Tfun c xs,k) = checkPTBndr current (Tcon c xs,k)
checkPTBndr current (y@(Tcon c xs),k) = 
  do { (tau,kind) <- getInfo y current c
     ; let check1 [] rng = return(rng,[])
           check1 (x:xs) (Karr m n) =
             do { env1 <- checkPTBndr current (x,m)
                ; (rng,env2) <- check1 xs n
                ; return(rng,env1++env2)}
           check1 (x:xs) kind = fail ("The type: "++show y++" is not well kinded")
           MK k2 = (unpoly kind)
     ; (rng,newenv) <- check1 xs k2
     ; unify rng k
     ; return newenv}
checkPTBndr current (Tstar n,Star m) | m==n+1 = return []
checkPTBndr current (Tkarr x y,k) =
  do { env1 <- checkPTBndr current (x,k)
     ; env2 <- checkPTBndr current (y,k)
     ; return(env1++env2) }
checkPTBndr current (y,k) = fail (show y++" :: "++show k++" is not well formed for a lhs.")
                
     

----------------------------------------------------

testRankN :: [[Dec]] -> FIO([[Dec]])
testRankN dss = fio $ runTC tcEnv0 (letExtend [] frag0 (testBndGroups dss))

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
     ; unifier <- fragMGU "checking testBndGroups" frag
     ; dss2 <- letExtend unifier frag (testBndGroups dss)
     ; return(ds2:dss2)
     }


wellTyped :: TcEnv -> Exp -> FIO(Sigma,Exp)
wellTyped env e = tcInFIO env (do { (t,term) <- infer e; typ <- nf t; return(typ,term)})

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
  do { (x,ns::[Eqn]) <- unTc e env
     ; if null ns
          then return x
          else fail ("Unresolved NEED: "++show ns)}

showFrag message frag =
  do { (Frag xs rs tenv eqs) <- zonk frag
     ; outputString ("\n********** Frag ***************" ++ message ++
           "\nBindings = "++plistf showBind "" (take 5 xs) ", " ""++
           "\nSkolem = "++show rs++
           "\nTypeEnv = "++ show tenv++
           "\nEqns = "++showEqn eqs++"\n*********************") }

showBind (x,(t,_,_)) = show x ++":"++show t


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
             do { truths <- zonk (assumptions env)
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
             do { ((t::Rho,_),oblig) <- collectEqn(inDisplay info (infer exp))
                ; t2 <- zonk t
                ; let (info2,tstring,eqs) = disp2 info (t2,oblig)
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


instance Display [(Var,(Sigma,Level,Exp))] where
  disp xs [] = (xs,"")
  disp xs ys = dispL disp xs ys "\n   "

instance Display (Var,(Sigma,Level,Exp)) where
  disp xs (v,(s,l,e)) = (zs,show v++": "++ans)
   where (zs,ans) = disp xs s


