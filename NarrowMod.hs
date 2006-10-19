-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Thu Oct 19 11:06:32 Pacific Daylight Time 2006
-- Omega Interpreter: version 1.2.2

module NarrowMod {-(narrow,defTree,DefTree,Rule(..),NS(..),Un,
                  NTerm(..),NMonad(..),Speaks(..),
                  value, freeTerm, andf, eqf, sampleRules,conF, funF,
                  term1,term2a,term3,term4,term5,term6,testN
                 )-}    where

import List(union,find,partition)
import Auxillary(maybeM,plistf,plist,DispElem(..),displays
                ,Display(..),DispInfo,initDI,drI,dlf2)
import Monad(when)

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

type Sol v t = [(Prob t,Rel t,Un v t)]
type ST z = (Int,Int,DispInfo z,Bool)

andR [x] = x
andR xs = AndR xs

andP [x] = x
andP xs = AndP xs


dispOf (x,y,d,z) = d

----------------------------------------------------------------
-- Ways to sisplay or print things

dProb :: NTerm z n v t => DispInfo z -> Prob t -> DispElem z
dProb _ (TermP t) = dterm t
dProb d (EqP(x,y)) = drI d [Ds "Equal ",dparen d x,Ds " ",dparen d y]
dProb d (AndP xs) = drI d [Ds "and(",dlf2 dProb xs "\n       ",Ds ")"]

dRel :: NTerm z n v t => DispInfo z -> Rel t -> DispElem z
dRel d (EqR(x,y)) = drI d [Ds "Equal ",dparen d x,Ds " ",dparen d y]
dRel d (AndR xs) = drI d [Ds "and(",dlf2 dRel xs "\n    ",Ds ")\n"]

sProb (state@(a,b,disp,c)) prob = dProb disp prob


dparen d x = case projN x of
            VarN _ -> dterm x
            FunN _ _ -> dterm x
            ConN _ _ -> drI d [Ds "(",dterm x,Ds ")"]

dUn :: NTerm z n v t => DispInfo z -> Un v t -> DispElem z
dUn d xs = dlf2 (\ d (v,t) -> drI d [dvar v, Ds "=", dterm t]) xs ", "

dSol :: NTerm z n v t => DispInfo z -> (Prob t,Rel t,Un v t) -> DispElem z
dSol d (prob,ts,u) = drI d [dProb d prob,Ds " where ", dUn d u]


dSols :: NTerm z n v t => ST z -> Sol v t -> DispElem z
dSols (_,_,d,_) ss = dl (dSol d) ss "\n "


warnS:: Speaks m z => ST z -> [DispElem z] -> m(ST z)
warnS (state@(a,b,disp,c)) elems =
    do { d2 <- warnDN disp elems; return(a,b,d2,c)};

{-
showSol:: NMonad z n v t m => ST z -> [Sol v t] -> m(ST z)
showSol (a,b,disp,c) ss =
    do { d2 <- warnDN disp [dSols disp ss]; return(a,b,d2,c) }
-}


valueP (TermP t) = value t
valueP _ = False


decStep (nsteps,nsolution,disp,bool) = (nsteps - 1,nsolution,disp,bool)
decSol  (nsteps,nsolution,disp,bool) = (nsteps,nsolution - 1,disp,bool)
exceeded (nsteps,nsolution,disp,bool) = nsteps < 0
noMoreNeeded (nsteps,nsolution,disp,bool) = nsolution < 0
tooMany (nsteps,nsolution,disp,_) =  (nsteps,nsolution,disp,True)

traceSteps (steps,count,d,exceeded) truths ys =
  do { verbose <- showStepN
     ; d1 <- whenDN verbose d
         [dsh steps, Ds "\nNarrowing the list (looking for "
         ,dsh count, Ds " solutions)\n",Ds "   "
         ,dlt (map fst ys) "\n   ",Ds "\nwith truths:\n   "
         ,dlt (map (\(x,y) -> eqf x y) truths) "\n   ", Ds "\n"]
     ; when verbose wait
     ; return (steps,count,d1,exceeded)
     }


traceSteps2 (steps,count,d,exceeded) (problems@((ps,truths,us):_)) found =
  do { verbose <- showStepN
     ; let f d (prob,truth,unifier) =
              Dr [dProb d prob,if null unifier
                                  then Ds "\n"
                                  else Dr[Ds " where ",dUn d (take 3 unifier)]]
     ; d1 <- whenDN verbose d
         [Ds "\n-------------------------------------\n"
         ,dsh steps, Ds " Narrowing the list (looking for "
         ,dsh count, Ds " solutions) found ",Ds (show (length found)),Ds "\n",Ds "   "
         ,dlf2 f problems "\n   ",Ds "\nwith truths:\n   "
         ,dRel d truths, Ds "\n"]
     ; when verbose wait
     ; return (steps,count,d1,exceeded)
     }

traceResult (steps,count,d,exceeded) cntxt un =
  do { verbose <- showStepN
     ; d1 <- whenDN verbose d
              [Ds "\n*********************"
              ,Ds "\nFound a solution for:\n  ",Ds cntxt,Ds "\n  ",dUn d un]
     ; return(steps,count,d1,exceeded)}


-- A unifer, u1, is more general than another unifier, u2, iff
-- every binding in u1 appears in u2. For example [p=a] is more
-- general than [b=#0, p=a] and also more general than [b=#(1+c), p=a]
moreGen :: NTerm z n v t => Un v t -> Un v t -> Bool
moreGen [] u2 = True
moreGen (p:ps) u2 = elem p u2 && moreGen ps u2

-- Add a solution, only every previous solution is not more general
addSol n@(t,ts,new) us =
   if (all (\ (t,ts,old) -> not(moreGen old new)) us)
      then n:(filter (\ (t,ts,old) -> not(moreGen new old)) us)
      else us

push u (prob,truths,u2) = (prob,truths,u2 `o` u)

narr:: NMonad z n v t m => String -> ST z -> Sol v t -> Sol v t -> m(Sol v t,ST z)
narr cntxt s [] foundsols = return(reverse foundsols,s)
narr cntxt s problems foundsols | exceeded s = return(reverse foundsols,tooMany s)
narr cntxt s problems foundsols | noMoreNeeded s = return(reverse foundsols,s)
narr cntxt s ((t,ts,un):more) foundsols | valueP t =
  do { s1 <- traceResult s cntxt un
     ; narr cntxt (decSol s1) more (addSol (t,ts,un) foundsols)}
narr cntxt s (problems@((p,truths,u):more)) foundsols =
  do { s1 <- traceSteps2 s problems foundsols
     ; (newprobs,s2) <- stepProb s1 p truths
     ; narr cntxt (decStep s2) (more ++ map (push u) newprobs) foundsols }

stepProb::  NMonad z n v t m => ST z -> Prob t -> Rel t -> m(Sol v t,ST z)
stepProb s (prob@(EqP(x,y))) truths =
  maybeM (rewNestedEqual (x,y))
         (\ (new,u1) -> do { truths2 <- subRels u1 truths
                           ; return([(TermP new,truths2,u1)],s)}) $
  maybeM (rewEqN (x,y))
         (\ u1 -> do { truths2 <- subRels u1 truths
                     ; return([(TermP success,truths2,u1)],s)})
         (case truths `implies` (x,y) of
            Just u1 -> do { s1 <- warnS s [Ds "\nThe term:\n   ", sProb s prob, Ds "\nis implied by the truths."]
                          ; truths2 <- subRels u1 truths
                          ; return([(TermP success,truths2,u1)],s1)}
            Nothing -> stepEq s (x,y) truths)

stepProb s (TermP t) truths = stepTerm s t truths
stepProb s (AndP []) truths = return([(TermP success,truths,[])],s)
stepProb s (AndP [p]) truths = stepProb s p truths
stepProb (s@(nstep,nsol,d0,ex)) (AndP (p:ps)) truths =
  do { let (d1,cntxt) = displays d0 [dProb d0 p]
           newS = (20,2,d1,False)
     ; (ans,s1@(_,_,d2,_)) <- narr ("And sub-problem\n  "++cntxt) newS [(p,truths,[])] []
     ; let nextS = (nstep -1,nsol,d2,ex)
     ; case ans of
         [] -> return([],nextS)
         [(TermP x,ts1,u1)] | x==success ->
            return([(andP(map (subProb u1) ps),ts1,u1)],nextS)
         new -> let add (p,ts,u1) = (andP(map (subProb u1) ps++[p]),ts,u1)
                in return(map add new,nextS)}

displaysN (x,y,d0,z) elems = ((x,y,d1,z),ans)
  where (d1,ans) = displays d0 elems

implies::  NTerm z n v t => Rel t -> (t,t) -> Maybe(Un v t)
implies (EqR(a,b)) (x,y) =
   case mguN [(x,a),(y,b)] of
     Nothing -> mguN [(x,b),(y,a)]
     Just u -> Just u
implies (AndR []) (x,y) = Nothing
implies (AndR (r:rs)) (x,y) =
  case implies r (x,y) of
    Nothing -> implies (AndR rs) (x,y)
    Just u -> Just u

stepEq::  NMonad z n v t m => ST z -> (t,t) -> Rel t -> m(Sol v t,ST z)
stepEq s0 (a,b) truths =
 case (projN a,projN b) of
  (VarN x,VarN y) | x==y -> return([(TermP success,truths,[])],s0)
  (VarN x,VarN y) ->
    do { (u,s1) <- mguV s0 truths [(varN x,varN y)]
       ; truths2 <- subRels u truths
       ; return([(TermP success,truths2,u)],s1)}
  (VarN s,ConN nm ts) | (properSubTerm s b) -> return ([],s0)
  (ConN nm ts,VarN s) | (properSubTerm s a) -> return ([],s0)
  (VarN s,ConN nm ts) ->
    do { vs <- mapM termFresh ts
       ; (u,s1) <- mguV s0 truths [(a,con nm vs)]
       ; truths2 <- subRels u truths
       ; return([(EqP (subN u a,subN u b),truths2,u)],s1)}
  (ConN nm ts,VarN s) ->
    do { vs <- mapM termFresh ts
       ; (u,s1) <- mguV s0 truths [(b,con nm vs)]
       ; truths2 <- subRels u truths
       ; return([(EqP (subN u a,subN u b),truths2,u)],s1)}
  (VarN s,FunN _ _) | False ->  -- not (occursN s b) ->
    do { t1 <- normN b
       ; (u,s1) <- mguV s0 truths [(varN s,t1)]
       ; truths2 <- subRels u truths
       ; return([(TermP success,truths2,u)],s1)}
  (FunN _ _,VarN s) | False -> -- not (occursN s a) ->
    do { t1 <- normN a
       ; (u,s1) <- mguV s0 truths [(varN s,t1)]
       ; truths2 <- subRels u truths
       ; return([(TermP success,truths2,u)],s1)}
  (FunN _ _,FunN _ _) | a==b -> return([(TermP success,truths,[])],s0)
  (FunN nm args,FunN nm2 args2) ->
    do { (ansA,s1) <- stepTerm s0 a truths
       ; (ansB,s2) <- stepTerm s1 b truths
       ; let extra = []
           {- if nm /= nm2
                    then []
                    else case mguN (zip args args2) of
                          Nothing -> []
                          Just u -> [(TermP success,subRels u truths,u)]
           -}
       -- we are only going to pursue one path, so choose one
       ; case fewestVar ansA a ansB b of
           (bool,ans,term) -> return(extra ++ map (buildQ bool term) ans,s2)}
  (FunN nm args, _) ->
    do { (ans,s1) <- stepTerm s0 a truths
       ; return(map (buildQ True b) ans,s1)}
  (_,FunN nm args) ->
    do { (ans,s1) <- stepTerm s0 b truths
       ; return(map (buildQ False a) ans,s1)}
  (ConN n xs,ConN m ys) | n /= m -> return([],s0)
  (t1@(ConN n xs),t2@(ConN m ys)) | n==m ->
    case (xs,ys) of
     ([],[]) -> return([(TermP success,truths,[])],s0)
     ([x],[y]) -> return([(EqP(x,y),truths,[])],s0)
     (_,_) -> return([(andP(zipWith (curry EqP) xs ys),truths,[])],s0)


simpRel (EqR(x,y)) =
  do { let start = EqP(x,y)
     ; ans <- stepEq (10,2,initDI,False) (x,y) (AndR [])
     ; case ans of
        ([(EqP(a,b),_,[])],(_,_,_,False)) -> simpRel (EqR(a,b))
        other -> return(EqR(x,y))
     }



mguV :: NMonad z n v t m => ST z -> Rel t -> [(t,t)] -> m(Un v t,ST z)
mguV s0 truths pairs =
  case mguEither pairs of
    Left u2 -> return(u2,s0)
    Right ("Rigid",v,t) -> fail ("the supposedly polymorphic variable '"++name++
                                 "'\narising from a type signature at "++loc++
                                 "\nis forced by context to be "++show t)
       where (name,loc) = locInfo v
    Right (s,t1,t2) -> fail ("Unification of (var,term) failed, this is impossible\n"++show pairs)


fewestVar xAns xterm yAns yterm =
     if xn <= yn then (True,xAns,yterm) else (False,yAns,xterm)
  where count (term,truths,unifier) = length unifier
        xn = sum(map count xAns)
        yn = sum(map count yAns)

-- True means put the problem on left, False means on right
buildQ True  y (TermP x,ts,u) = (EqP(x,subN u y),ts,u)
buildQ False y (TermP x,ts,u) = (EqP(subN u y,x),ts,u)
buildQ _ _ prob = error ("Non term problem returned from stepProb  in equality")


stepTerm:: NMonad z n v t m => ST z -> t -> Rel t -> m(Sol v t,ST z)
stepTerm s0 term truths =
  case projN term of
   (VarN _) -> return([(TermP term,truths,[])],s0)
               -- VarN case Should be unreachable, if the valueP test works.
   (FunN nm _) -> maybeM
                   (rewN term)
                   (\ (t,u) -> do { truths2 <- subRels u truths
                                  ; return([(TermP t,truths2,u)],s0)})
                   (do { tree <- (treeOfN nm)
                       ; stepTree nm term truths tree s0})
   (ConN _ _) -> case pathTo1stFunN term of
                  Just path ->
                    do { let exp = getTermAtPath path term
                       ; (ans,s1) <- stepTerm s0 exp truths
                       ; return(map (reBuild term path) ans,s1)}
                  Nothing -> return([(TermP term,truths,[])],s0)
   (RelN (EqR(x,y))) -> stepProb s0 (EqP(x,y)) truths

reBuild term path (TermP x,ts,u) = (problem,ts,u)
    where problem = TermP(subN u (insertNewTermAtPath term path x))


stepTree:: NMonad z n v t m =>
           n ->  t -> Rel t -> DefTree v t -> ST z -> m(Sol v t,ST z)
stepTree name t truths (Leaf pat free lhs rhs) s0 =
   maybeM (matches t pat)                             -- test
          (applyLfRule s0 t truths (free,lhs,rhs))    -- if successful
          (return ([],s0))                            -- if failure
stepTree name term truths (Branchx termX path ts) s0 =
   maybeM (matches term termX)
          (applyBranchRule s0 name term truths (path,ts))
          (return ([],s0))

matches :: NMonad z n v t m => t -> t -> m (Maybe (t,[(v,t)]))
matches term pat =
  do { p <- freshen pat;
     ; case mguN[(p,term)] of
         Nothing -> return Nothing
         Just u -> return(Just(subN u term,u))}

-- When applying a Branchx rule, find the deepest rules that match, and
-- use their answers. If there are any. Note, that there may be more than
-- one subtree that matches, if so, combine all the answers. If no
-- subtree matches, then use the root, and narrow the subterm pointed
-- to by path. Get multiple answers, by rebuilding the term, once for
-- for each answer for the subterm pointed to by path.

applyBranchRule s0 name term truths (path,subtrees) (matched,mU) =
  do { (ansListList,s1) <- mapThread s0 (stepTree name term truths) subtrees
     ; let new = (getTermAtPath path term)
     ; case all null ansListList of
        False -> return(concat ansListList,s1) -- At least 1 answer use them
        True -> case projN new of -- No subtree applies so use root
                 (FunN nm _) ->
                     do { (ans,s2) <- stepTerm s1 new truths
                        ; return(map (reBuild term path) ans,s2)}
                 other -> let newest = insertNewTermAtPath matched path new
                          in if newest==term
                                 then noProgress initDI name term
                                 else do { truths2 <- subRels mU truths
                                         ; return ([(TermP newest,truths2,mU)],s1)}}

-- In applyLfRule, We first match the term against lhs,
-- recall matchN [(lhs,term)] only binds variables in lhs, so if
-- this succeeds, the unifier is only usefull to apply to "rhs2".
-- It mentions no no variables in "t" or "truths" since the vars
-- in "lhs2" are fresh. It is good to match, rather than unify,
-- since it avoids introducing new variables some times. If
-- matching fails, we try unification.

applyLfRule s0 term truths rule uselessUnifier =
  do { (lhs2,rhs2) <- freshX rule
     ; case matchN [] [(lhs2,term)] of
         Just unifier ->
           return ([(TermP(subN unifier rhs2),truths,[])],s0)
         Nothing ->
           case mguN [(lhs2,term)] of
             Just u2 -> let important = freeTerm term
                            u3 = orientBindings important u2
                            good (var,term) = elem var important
                        in do { truths2 <- subRels u3 truths
                              ; return ([(TermP(subN u3 rhs2),truths2,filter good u3)],s0)}
             Nothing -> (return ([],s0)) }

orientBindings free [] = []
orientBindings free ((p@(var,term)):more) =
  let rest = orientBindings free more
  in case projN term of
      VarN nm -> if elem var free
                    then (nm,varN var):rest
                    else p:rest
      _ -> p:rest


subTerms u xs = map (subN u) xs

subRels u (EqR(x,y)) =
  do { a <- normN(subN u x); b <- normN(subN u y); simpRel(EqR(a,b))}
subRels u (AndR rs) = do { ans <- mapM (subRels u) rs; return(AndR ans)}

subProb u (EqP(x,y)) = EqP(subN u x,subN u y)
subProb u (AndP rs) = AndP (map (subProb u) rs)
subProb u (TermP x) = TermP(subN u x)

o new old = composeUn new old

---------------------------------------------------

type Un var term = [(var,term)]

type Path = [Int]

data DefTree var term
  = Leaf term [var] term term
  | Branchx term Path [DefTree var term]

data Rule name var term = NarR(name,[([var],[term],term)])

data Chain var term
  = Root term
  | Next term Path (Chain var term)

---------------------------------------------------------
-- primitive operations on terms, variables, and the monad

class (Show name,Eq name,Display name z
      ,Show var, Eq var, Display var z
      ,Show term,Eq term,Display term z) =>
      NTerm z name var term |
      term -> var, term -> name, name -> term, var -> term
      ,term -> z  where
  projN :: term -> NS name var term
  injN :: NS name var term -> term
  varN :: var -> term
  subN :: Un var term -> term -> term
  --mguN :: Monad m => [(term,term)] -> m(Un var term)
  mguEither :: [(term,term)] -> Either (Un var term) (String,term,term)
  matchN :: Monad m => Un var term -> [(term,term)] -> m(Un var term)
  success :: term
  andName :: name
  varWild :: var -> term
  termWild :: term -> term
  equalTerm:: term -> term -> term
  equalP:: term -> Bool
  equalParts:: term -> (term,term)
  dterm:: term -> DispElem z
  dname:: name -> DispElem z
  dvar:: var -> DispElem z
  locInfo:: term -> (String,String)
  -- The next 3 are strictly for the sample definitions
  samples :: [(var,term)]
  toName :: String -> name
  varF :: Integer -> term


mguN xs =
  case mguEither xs of
    Left ans -> return ans
    Right (s,x,y) -> fail s


class Monad m => Speaks m z | m -> z, z -> m where
  wait :: m ()
  delayN :: m Bool
  forbidN:: m Bool
  showStepN:: m Bool
  whenDN :: Bool -> DispInfo z -> [DispElem z] -> m(DispInfo z)
  warnN :: [DispElem z] -> m(DispInfo z)
  warnDN :: DispInfo z -> [DispElem z] -> m(DispInfo z)


class (Speaks m z,NTerm z n v t) => NMonad z n v t m | z -> n, z -> v, z -> t where
  termFresh :: t -> m t
  varFresh :: v -> m t
  treeOfN :: n -> m (DefTree v t)
  treeOfN s = return(treeOf s)
  normN :: t -> m t
  rewN:: t -> m(Maybe(t,Un v t))
  rewEqN:: (t,t) -> m(Maybe(Un v t))
  rewNestedEqual:: (t,t) -> m(Maybe(t,Un v t))



dl elemf ts comma = Dlf f ts comma
  where f d x = displays d [elemf x]

dlt ts comma = dl dterm ts comma
dlsh ts comma = dl dsh ts comma
dsh n = Ds (show n)

-- dispUn :: NMonad z n v t m => (Un v t,DispInfo z) -> m(DispInfo z)
dispUn (us,d0) = warnDN d0 [Ds"[",Dlf f us ",",Ds "]"]
  where f d (v,t) = displays d [Ds "(",dvar v,Ds ",",dterm t,Ds ")"]

fun n ys = injN(FunN n ys)
con n ys = injN(ConN n ys)
eq [x,y] = injN(RelN (EqR (x,y)))
eqf x y = equalTerm x y
andf x y = fun andName [x,y]
andParts x = case projN x of
               FunN n [x,y] | n==andName -> (x,y)
               _ -> error ("term is not of form {and x y} "++show x)



--------------------------------------------------------------
-- Show instances

instance (Show n,Show v,NTerm z n v t) => Show (Rule n v t) where
  show (NarR(nm,xs)) =  "\n"++plistf f "" xs "\n" ""
    where f (vs,xs,t) = plistf show "[" vs "," "]"++"{"++show nm++" "++plistf h "" xs " " ""++"} = "++show t
          h x | conP x = "("++show x++")"
          h a = show a
          conP x = case (projN x) of { ConN _ (z:zs) -> True; _ -> False}


tree2string tree = indent 0 tree
  where indent n (Leaf term free lhs rhs ) = blanks n ++ "Leaf " -- ++ (show term) ++  ",   "
                                            ++ show lhs ++ " --> "++show rhs
        indent n (Branchx term pos tree) = blanks n ++
          "Branchx " ++ (show pos) ++ " " ++ (show term) ++
          concat (map (\x -> indent (n+1) x) tree)
        blanks n = "\n" ++ (take n (repeat ' '))

{-
instance (Show v, Show t) => Show (DefTree v t) where
  show x = tree2string x
-}
----------------------------------------------------------------
-- Operations on Terms

freshX :: NMonad z n v t m => ([v],t,t) -> m (t,t)
freshX (vs,ps,term) =
  do { ns <- mapM varFresh vs
     ; let subT = zip vs ns
     ; return(subN subT ps,subN subT term)}


freshen :: (NMonad z n v t m) => t -> m t
freshen x =
  case projN x of
   (VarN s) -> varFresh s
   (FunN n xs) -> do { ys <- mapM freshen xs; return(fun n ys)}
   (ConN n xs) -> do { ys <- mapM freshen xs; return(con n ys)}
   (RelN (EqR (x,y))) -> do { a <- freshen x; b <- freshen y; return(eq [a,b]) }

liftN f x = f (projN x)

value :: (NTerm z n v t) => t -> Bool
value x = liftN val x
 where val (VarN a) = True
       val (ConN s ts) = all value ts
       val (FunN s ts) = False
       val (RelN x) = False

freeTerm :: NTerm z n v t => t -> [v]
freeTerm x = liftN free x
  where free(VarN s) = [s]
        free(ConN t ts) = foldr (add freeTerm) [] ts
        free(FunN t ts) = foldr (add freeTerm) [] ts
        free (RelN (EqR(x,y))) = union (freeTerm x) (freeTerm y)
        add freeF xs ys = union (freeF xs) ys



occursN:: NTerm z n v t => v -> t -> Bool
occursN v t = elem v (freeTerm t)


-- If narrowing (Eq v (Con 2 v)) where v is a subterm
-- of a Constructor which is not nested inside a function
-- (i.e. something like (Eq v (Con {plus v 4} 2)) might be ok.)
-- then the narrowing must fail, as no terms are infinite.

properSubTerm:: NTerm z n v t => v -> t -> Bool
properSubTerm v x = liftN free x
  where free(VarN s) = s==v
        free(ConN t ts) = any (properSubTerm v) ts
        free(FunN t ts) = False
        free(RelN x) = False


------------------------------------------------------
-- unifiers

-- composeUn :: Un v t -> Un v t -> Un v t
composeUn s1 s2 = ([(u,subN s1 t) | (u,t) <- s2] ++ s1)

subTwoList :: NTerm z n v t => Un v t -> [(t,t)] -> [(t,t)]
subTwoList env xs = map f xs where f (x,y) = (subN env x,subN env y)

pushUnifier u1 [] = []
pushUnifier u1 ((exp,u2):xs) = (exp,composeUn u2 u1):pushUnifier u1 xs

----------------------------------------------------------------
-- Creating Definitional Trees

-- makeChainL (FunN "eq" [ConN "Zero"[],ConN "Zero"[]])
-- [Next {eq Zero Zero} [0] (Next {eq _ Zero} [1] (Root {eq _ _}))
-- ,Next {eq Zero Zero} [1] (Next {eq Zero _} [0] (Root {eq _ _}))
-- ]

makeChainL :: NTerm z n v t => t -> [Chain v t]
makeChainL x = liftN h x
  where h (FunN name args) =
          do { zs <- generalizeL 0 args
             ; matchLx name args zs}

matchLx :: NTerm z n v t => n -> [t] -> (Path,[t]) -> [Chain v t]
matchLx name args ([], newArgs) = return (Root (fun name newArgs))
matchLx name args (h:t, newArgs) =
  do { tail <- makeChainL (fun name newArgs)
     ; return (Next (fun name args) (h:t) tail)}


-- If we're computing a DefTree for {f a0 a1 a2 a3} then we call
-- generalizeL 0 [a0,a1,a2,a3]

generalizeL :: NTerm z n v t => Int -> [t] -> [(Path,[t])]
generalizeL _ [] = return ([],[])
generalizeL n (arg_n : args) = liftN h arg_n
  where h (VarN vv) =
          do { (newPos, newRest) <- generalizeL (n+1) args
             ; return (newPos, varWild vv : newRest)}
        h (ConN name ts) = map match (generalizeL 0 ts) ++
                           foldr add [] (generalizeL (n+1) args)
          where match ([], _) = ([n], termWild arg_n : args)
                match (a:b, newArgs) = (n:a:b, con name newArgs : args)
                add (a:b, newRest) ans = (a:b, con name ts : newRest):ans
                add ([], newRest) ans = ans

makeTreePath free lhs rhs (Root term) = Leaf term free lhs rhs
makeTreePath free lhs rhs (Next term pos chain) = revMore (Leaf term free lhs rhs) pos chain
  where revMore tree pos (Root term) = Branchx term pos [tree]
        revMore tree p1 (Next term pos chain)
          = revMore (Branchx term p1 [tree]) pos chain

branchP (Branchx _ _ _) = True
branchP _ = False


-- There is an invariant here. To succeed, makeTreeL must be called with
-- either a single leaf, or a list of Branchx terms, all of which have
-- a common root term, and position.

makeTreeL :: Eq t => [DefTree v t] -> [DefTree v t]
makeTreeL [Leaf x free lhs rhs ] = [Leaf x free lhs rhs]
makeTreeL (Branchx term pos tree : rest)
  | all branchP rest &&
    all (== pos) (map (\(Branchx _ p _) -> p) rest)
  = do { zs <- mapM makeTreeL (partition children)
       ; return( Branchx term pos zs)}
  where children = concat (map (\(Branchx _ _ t) -> t)
                               (Branchx term pos tree : rest))
        partition [] = []
        partition (Leaf x free lhs rhs : rest) = [Leaf x free lhs rhs] : partition rest
        partition (Branchx term pos tree : rest)
          = (Branchx term pos tree : a) : partition b
          where (a, b) = aux rest ([],[])
                -- "aux" splits "rest" into two lists
                -- a = those Branch trees whose lhs == term
                -- b = all other trees in "rest"
                aux [] z = z
                aux (Leaf t free lhs rhs : rest) (x,y)
                  = if (t==term)
                    then aux rest (Leaf t free lhs rhs : x, y)
                    else aux rest (x, Leaf t free lhs rhs : y)
                aux (Branchx t p c : rest) (x,y)
                  = if (t==term)
                    then aux rest (Branchx t p c : x, y)
                    else aux rest (x, Branchx t p c : y)
makeTreeL other = []

renameVarN :: NTerm z n v t => t -> t
renameVarN x = liftN h x
  where h (VarN vv) = varWild vv
        h (ConN name args) = con name (map renameVarN args)
        h (FunN name args) = fun name (map renameVarN args)
        h (RelN (EqR(x,y))) = eq [renameVarN x, renameVarN y]

mainY :: NTerm z n v t => n -> [([v],[t],t)] -> [DefTree v t]
mainY name patternList = do { zs <- mapM (f12 name) patternList
                            ; makeTreeL zs}
f12 name (free2,lhs,rhs) = map (makeTreePath free2 lhs2 rhs)
                               (makeChainL (renameVarN lhs2))
   where lhs2 = (fun name lhs)

defTree :: NTerm z n v t => Rule n v t -> [DefTree v t]
defTree (NarR(name,zs)) = mainY name zs


------------------------------------------------------
-- operations on Paths

getTermAtPath :: NTerm z n v t => [Int] -> t -> t
getTermAtPath [] x = x
getTermAtPath (n:ns) x = liftN h x
  where h (FunN nm ts) = getTermAtPath ns (ts !! n)
        h (ConN nm ts) = getTermAtPath ns (ts !! n)
        h (RelN (EqR (x,y))) = getTermAtPath ns ([x,y] !! n)

insertNewTermAtPath old [] new = new
insertNewTermAtPath old (path@(n:ns)) new =
  case projN old of
    FunN name ts -> fun name (insertAt n (insertNewTermAtPath (ts !! n) ns new) ts)
    ConN name ts -> con name (insertAt n (insertNewTermAtPath (ts !! n) ns new) ts)
    RelN (EqR(t0,t1)) -> let ts = [t0,t1]
                         in eq (insertAt n (insertNewTermAtPath (ts !! n) ns new) ts)


pathTo1stFunN :: NTerm z n v t => t  -> Maybe Path
pathTo1stFunN x = liftN h x
  where h(FunN _ _) = Just []
        h(RelN (EqR(x,y))) = firstPathInList 0 (map pathTo1stFunN [x,y])
        h(VarN _) = Nothing
        h(ConN s ts) = firstPathInList 0 (map pathTo1stFunN ts)


firstPathInList n [] = Nothing
firstPathInList n ((Just path):ys) = Just(n:path)
firstPathInList n (Nothing : ys) = firstPathInList (n+1) ys

insertAt 0 x (t:ts) = x:ts
insertAt n x (t:ts) = t : insertAt (n-1) x ts

subInPlace :: NTerm z n v t => ((t,Un v t) -> c) -> Path -> t -> [(t,Un v t)] -> [c]
subInPlace k [] term subterms = map k subterms
subInPlace k (n:ns) x subterms = liftN h x
  where h (FunN name ts) = subInPlace k2 ns (ts !! n) subterms
            where k2 (x,u) = k((fun name (insertAt n x ts)),u)
        h (ConN name ts) = subInPlace k2 ns (ts !! n) subterms
            where k2 (x,u) = k((con name (insertAt n x ts)),u)
        h (RelN (EqR(term1,term2))) = subInPlace k2 ns ([term1,term2] !! n) subterms
            where k2 (x,u) = k((eq (insertAt n x [term1,term2])),u)

duplicateTerm :: NTerm z n v t => Un v t -> Path -> t -> [(t,Un v t)] -> [(t,Un v t)]
duplicateTerm u path term subTs = pushUnifier u (subInPlace app path term subTs)
  where app (x,u) = (subN u x,u)


-------------------------------------------------------------------------
-- The old version of narrowing
------------------------------------------------------------
-- kinds of answers narrowing may find. We want to distingush
-- running out of resources from no answers.

data NResult v t =
    Answers  [(t,Un v t)]
  | Exceeded [(t,Un v t)]


nCons:: NTerm z n v t => (t,Un v t) -> NResult v t -> NResult v t
nCons x (Answers xs) = Answers(x : xs)
nCons x (Exceeded xs) = Exceeded(x: xs)

nAppend xs (Answers ys) = Answers(xs++ys)
nAppend xs (Exceeded ys) = Exceeded(xs++ys)

-------------------------------------------------------
type Eqs t = [(t,t)]

{-  NOTE ************
     Narrow should amnipulate [(t,Eqs t,Un vt)] because matching against
     a truth changes the truths for each possibility
-}

narrow:: (Eq t,NMonad z n v t m) => (Int,Int) -> Eqs t -> [(t,Un v t)] -> DispInfo z -> m (NResult v t,DispInfo z)
narrow (count,steps) truths [] d0 = return(Answers [],d0)
narrow (count,steps) truths xs d0 | (count::Int) <= 0 = return(Answers [],d0)
narrow (count,steps) truths xs d0 | (steps::Int) <= 0 = return(Exceeded [],d0)
narrow (count,steps) truths (ys@((x,u):xs)) d0 | value x =
   do { (_,_,d1,_) <- traceSteps (steps,count,d0,False) truths ys
      ; (ys,d2) <-(narrow (count - 1,steps) truths xs d1)
      ; return (nCons (x,u) ys,d2) }
narrow (count,steps) truths (ys@((x,u):xs)) d0 =
   do { (_,_,d1,_) <- traceSteps (steps,count,d0,False) truths ys; liftN (h d1) x }
  where h d0 (FunN nm [left,right]) | nm==andName =
           do { (ans,d1) <- oneStep d0 left truths
              ; let newRight (newleft,u2) =
                      let u3 = composeUn u2 u
                      in (subN u2 right,u3)
              ; case ans of
                  [(ans,u2)] | ans==success ->
                     narrow (count,steps-1) truths ((newRight (ans,u2)):xs) d1
                  other ->
                     let fix (pair@(left',u)) =
                             let (right',u2) = newRight pair
                             in (andf right' left',u2)
                     in narrow (count,steps-1) truths (xs++map fix other) d1}

        h d0 (FunN nm _) =
          do { ((n,values,terms),d1) <- oneStepVs d0 x truths
             ; let answers = pushUnifier u values
             ; (zs,d2) <- (narrow (count - n,steps - 1) truths (xs ++ (pushUnifier u terms)) d1)
             ; return(nAppend answers zs,d2)}
        h d0 _ = case pathTo1stFunN x of
               Just path ->
                 let exp = getTermAtPath path x
                 in do { ((n,values,exps),d1) <- oneStepVs d0 exp truths
                       ; let ys = duplicateTerm [] path x exps
                             vs = duplicateTerm [] path x values
                       ; (zs,d2) <- narrow (count-n,steps - 1) truths (xs ++ (pushUnifier u ys)) d1
                       ; return(nAppend (pushUnifier u vs) zs,d2)}
               Nothing -> do { (ys,d1) <- (narrow (count - 1,steps - 1) truths xs) d0
                             ; return (nCons (x,u) ys,d1) }




-- Split the steps into values and terms, always move
-- the values to the fron of the list

oneStep d0 x truths =
  do { ((n,vs,ps),d1) <- oneStepVs d0 x truths
     ; return(vs++ps,d1)
     }

-- Split the steps into values and terms, return
-- the number of values and separate the two

oneStepVs ::  (Eq t,NMonad z n v t m) =>
   DispInfo z -> t  -> Eqs t -> m ((Int,[(t,Un v t)],[(t,Un v t)]),DispInfo z)
oneStepVs d0 x truths =
  do { let h (RelN (EqR(a,b))) = eqStep d0 (truths,[]) x a b
           h (FunN nm _) = do { tree <- (treeOfN nm)
                              ; treeStep nm truths x tree d0 }
     ; (all,d1) <- liftN h x
     ; let (vs,terms) = partition (\ (v,u) -> value v) all
     ; return((length vs,vs,terms),d1)}

-- traceTruth :: (NMonad z n v t m) => [t] -> a -> m a
traceTruth d terms answer =
  do { verbose <- showStepN
     ; d2 <- whenDN verbose d
               [Ds "**** Using the truths ****\n   ",dlt terms "\n   ",Ds "\n"]
     ; return (answer,d2)
     }

-- when comparing 2 function calls like
-- {plus z #(1+w)} == {plus #(1+z) w}
-- one can choose to take 1 step on either
-- the left or right handside. In this case
-- the right hand side is a better choice since
-- it binds no variables to take a step since
-- the constructor #(1+Z) is in inductive
-- position. Choose the side that binds
-- the fewest variables.

chooseFewer xs ys = if xn <= yn then (True,xs) else (False,ys)
  where count (term,unifier) = length unifier
        xn = sum(map count xs)
        yn = sum(map count ys)

fewer infoA infoB =
     if (count infoA) <= (count infoB) then (True,infoA) else (False,infoB)
   where count (probs,truths,unifier) = length unifier



treeStep ::(Eq t,NMonad z n v t m) =>
            n -> Eqs t -> t -> DefTree v t -> DispInfo z -> m ([(t,Un v t)],DispInfo z)
treeStep name truths  t (Leaf pat free lhs rhs) d0 = maybeM (matches t pat) (ok d0) (return ([],d0))
  where ok d0 u3 = do { (lhs2,rhs2) <- freshX (free,lhs,rhs)
                   ; case matchN [] [(lhs2,t)] of
                       Just unifier -> return ([(subN unifier rhs2,[])],d0)
                         -- we're matching, so once applied to "rhs2",
                         -- the unifier is no longer useful, since it
                         -- binds no variables in "t". It is good to
                         -- match, rather than unify, since it avoids
                         -- introducing new variables some times. If
                         -- matching fails, we try unification.
                       Nothing -> case mguN [(lhs2,t)] of
                                    Just unifier -> return ([(subN unifier rhs2,unifier)],d0)
                                    Nothing -> return ([],d0) }
treeStep name truths term (Branchx termX path ts) d0 = maybeM (matches term termX) (ok d0) (return ([],d0))
  where ok d0 (tm,u) =
         do { (ws,d1) <- mapThread d0 (treeStep name truths term) ts
            ; let new = (getTermAtPath path term)
            ; if all null ws
                 then case projN new of
                       (FunN nm _) ->
                          do { (ans,d2) <- (oneStep d1 new truths)
                             ; return(duplicateTerm u path tm ans,d2)}
                       _ -> case duplicateTerm u path tm [(new,[])] of
                             zs@[(new,un)] -> if term==new
                                                 then noProgress d1 name term
                                                 else return (zs,d1)
                             zs -> return (zs,d1)
                 else return(concat ws,d1)}

mapThread d0 f [] = return([],d0)
mapThread d0 f (x:xs) =
  do { (y,d1) <- f x d0
     ; (ys,d2) <- mapThread d1 f xs
     ; return(y:ys,d2)}

-----------------------------------------------------------------------
-- Using truths (things known to be equal) and Lemmas.

match1Truth:: NTerm z n v t => t -> t -> [(t,t)] -> Maybe(Un v t)
match1Truth a b [] = Nothing
match1Truth a b ((x,y):more) =
   case (matchTruth a b x y) of
     Just u -> Just u
     Nothing -> match1Truth a b more

matchTruth a b x y =
  case mguN [(a,x),(b,y)] of
    Nothing -> mguN [(a,y),(b,x)]
    Just u -> Just u

match1Lemma:: NTerm z n v t => t -> [(t,t)] -> Maybe(t,Un v t)
match1Lemma a [] = Nothing
match1Lemma a ((lhs,rhs):more) =
   case mguN [(a,lhs)] of
     Nothing -> match1Lemma a more
     Just u -> Just(subN u rhs,u)


-----------------------------------------------------------------------
-- Comparing two things that are supposed to be equal

eqStep :: (Eq t,NMonad z n v t m) =>
       DispInfo z -> (Eqs t,Eqs t) -> t -> t -> t -> m ([(t,Un v t)],DispInfo z)
eqStep d0 (truths,lem) x a b =
     do { delay <- delayN
        ; d1 <- warnDN d0 [Ds "\n IN eq Step ",dterm a,Ds " = ",dterm b]
        ; case (match1Lemma a lem,match1Lemma b lem) of
           (Nothing,Nothing) ->
              case match1Truth a b truths of
               Just u -> do { d2 <- warnDN d1 [Ds "\n match truth\n ",Ds (show a++" = "++show b)
                                  ,Ds (show truths),Ds ("\n un = "++show u)
                                   ,Ds ("\n disp = "++show d1)]
                            ; traceTruth d2 [(eqf a b)] [(success,u)]}
               Nothing -> do { (ans,d1) <- h delay x (projN a) (projN b) d0
                             ; return(ans,d1)}
           (Just(t,u),Nothing) -> return ([(eqf t (subN u b),u)],d0)
           (Nothing,Just(t,u)) -> return ([(eqf (subN u a) t,u)],d0)

        }
  where h _ x (VarN s) (VarN t) d0 =
          if  s==t then return([(success,[])],d0)
                   else do { (u,d1) <- mguTruth d0 truths [(varN s,varN t)]
                           ; return([(success,u)],d1)}
        h _ x (VarN s) (ConN nm ts) d0 | (properSubTerm s b) = return ([],d0)
        h _ x (VarN s) (ConN nm ts) d0 =
          do { vs <- mapM termFresh ts
             ; (u,d1) <- mguTruth d0 truths [(a,con nm vs)]
             ; return([(subN u x,u)],d1)}
        h _ x (ConN nm ts) (VarN s) d0 | (properSubTerm s a) = return ([],d0)
        h _ x (ConN nm ts) (VarN s) d0 =
          do { vs <- mapM termFresh ts
             ; (u,d1) <- mguTruth d0 truths [(b,con nm vs)]
             ; return([(subN u x,u)],d1)}
        h True x (VarN s) term@(FunN _ _) d0 | not (occursN s b) =
          do { t1 <- normN (injN term)
             ; (u,d1) <- mguTruth d0 truths [(varN s,t1)]
             ; return([(success,u)],d1)}
        h True x term@(FunN _ _) (VarN s) d0 | not (occursN s a) =
          do { t1 <- normN (injN term)
             ; (u,d1) <- mguTruth d0 truths [(varN s,t1)]
             ; return([(success,u)],d1)}
        h _ x (FunN _ _) (FunN _ _) d0 | a==b =
          do { -- speak "A = B"
             ; return([(success,[])],d0) }
        h _ x (FunN nm args) (FunN nm2 args2) d0 =
          do { (ansA,d1) <- oneStep d0 a truths
             ; (ansB,d2) <- oneStep d1 b truths
             ; d3 <- warnDN d2 [Ds ("\n  ansB = "++show ansA),Ds ("\n  ansB = "++show ansB)]
             ; let (isA,ans) = chooseFewer ansA ansB
             ; let path = if isA then [0] else [1]
             ; return(duplicateTerm [] path x ans,d2)}
        h _ x (RelN (EqR(i,j))) (RelN (EqR(m,n))) d0 =
               fail "Bogus use of equality in narrowing"
               -- return ([(andf (eqf i m) (eqf j n),[])],d0)

        h _ x (FunN nm args) _ d0 =
          do { (ans,d1) <- oneStep d0 a truths
             ; return(duplicateTerm [] [0] x ans,d1)}
        h _ x _ (FunN nm args) d0 =
          do { (ans,d1) <- oneStep d0 b truths
             ; return(duplicateTerm [] [1] x ans,d1)}
        h _ x (ConN n xs) (ConN m ys) d0 | n /= m = return([],d0)
        h _ x (t1@(ConN n xs)) (t2@(ConN m ys)) d0 | n==m =
          case (xs,ys) of
           ([],[]) -> return([(success,[])],d0)
           ([x],[y]) -> return([(eqf x y,[])],d0)
           (_,_) -> return([(foldr andf success (zipWith eqf xs ys),[])],d0)


-----------------------------------------------------
-- Narrowing under truths.
-- We can use truths two ways.
--  1) when narrowing (a==b)
--     if either (a==b) or (b==a) is an element of the truths
--     then return (success,[])
--  2) During narrowing we generate a solution (term,sub) and
--     the substitution contains (v |-> t) and (v==t) or (t==v)
--     is in the truths. Then return (term,sub \\ [(v,t)])
-- Whenever we use either of these rules we would like to note
-- that we did, for reporting and debugging purposes.

isTruth:: NTerm z n v t => t -> t -> (t,t) -> Bool
isTruth a b (t1,t2) =
   (a,b) == (t1,t2) || (b,a) == (t1,t2)

elemTruths :: NTerm z n v t => t -> t -> [(t,t)] -> Bool
elemTruths a b truths = any (isTruth a b) truths

equate :: NTerm z n v t => [(t,t)] -> t -> t -> t
equate truths a b =
  if elemTruths a b truths
     then success
     else eqf a b

-- Remove a truth from a substitution.
-- And record which truths were used.

simpUn :: NTerm z n v t => Eqs t -> Un v t -> (Maybe[t],Un v t)
simpUn truths [] = (Nothing,[])
simpUn truths ((v,t):xs) =
  let (m,xs2) = simpUn truths xs
  in if elemTruths (varN v) t truths
        then (addM (eqf (varN v) t) m,xs2)
        else (m,(v,t):xs2)

addM t Nothing = Just[t]
addM t (Just xs) = Just (t:xs)

-- Take truths and a list of terms we want to unify.
-- Unify them, and remove any evident truths from the
-- substitution. Done in a monad so we can report which
-- truths we used.

-- mguTruth :: (NMonad z n v t m) => [(t,t)] -> [(t,t)] -> m [(v,t)]
mguTruth d0 truths xs =
  case mguN xs of
    Just un -> case simpUn truths un of
                 (Nothing,unifier) -> return (unifier,d0)
                 (Just used,unifier) -> traceTruth d0 used unifier
    Nothing -> fail "mguTruth"

----------------------------------------------------------------
noProgress d0 name term =
  fail ("While narrowing, the term:\n   "++show term++
        "\nNo rule for "++show name++" matched. Either the rules are incomplete, or a lemma is needed.")


-- showStep :: (Speaks m z) => String -> (t,Un v t) -> m ()
showStep indent (x,u) =
   warnN [Ds indent,dterm x,Ds ":\n",Dlf f u "\n"] >> return ()
 where f d (v,t) = displays d [Ds "    ",dvar v,Ds " = ",dterm t]

-- showStep2 :: (Speaks m z) => DispInfo z -> String -> (t,Un v t) -> m(DispInfo z)
showStep2 d indent (x,u) =
   warnDN d [Ds indent,dterm x,Ds ":\n",Dlf f u "\n"]
 where f d (v,t) = displays d [Ds "    ",dvar v,Ds " = ",dterm t]

{-
] >> g "    " u
  where g i [] = return ()
        g i ((v,t):xs) = do { warnN [Ds i,dvar v,Ds " = ",dterm t,Ds "\n"]
                            ; g i xs}
       -- (i++show v++" = "++show t++"\n")++(g i xs)
-}

{-
hnf :: NMonad z n v t m => Un v t -> t -> m [(t,Un v t)]
hnf u x = liftN h x
  where h (VarN s) = return [(varN s,u)]
        h (FunN nm _) =
          do { ans <- oneStep truths x
             ; let add [] = return []
                   add ((t,u2):ys) =
                      do { as <- hnf (composeUn u2 u) t
                         ; bs <- add ys
                         ; return(as++bs)}
             ; add ans}
        h (ConN _ _) = return [(x,u)]
-}
---------------------------------------------------------------
-- some sample rules, and a default treeOfN
-- These can be commented out, if desired

sampleRules :: NTerm z n v t =>
              (String -> [t] -> t) ->
              (String -> [t] -> t) ->
              [(v,t)] -> [Rule n v t]
sampleRules fun con
            [(s,_)                     -- Prop (Success)
            ,(xs,_),(ys,_)             -- Lists (Nil, Cons)
            ,(w,_),(x,_),(y,_),(z,_)   -- Sets (Univ,Empty _,Plus _ _, Times _ _)
            ,(a,_),(b,_)               -- *0
            ,(m,_),(n,_)               -- Nat (Zero, Succ)
            ,(t,_)                     -- Totality (Total, Partial)
            ] =
    [NarR(toName "and",
             [([s],[success,varN s],varN s)
             ])
    ,NarR(toName "take",
              [([xs],[con "Zero" [] ,varN xs],con "Nil" [])
              ,([n],[con "Succ" [varN n],con "Nil" []],con "Nil" [])
              ,([n,a,xs],[con "Succ" [varN n],con "Cons" [varN a, varN xs]]
                         ,con "Cons" [varN a,fun "take" [varN n,varN xs]])
              ])
    ,NarR(toName "acker",
              [([n],[con "Zero" [], varN n],
                con "Succ" [varN n])
              ,([m],[con "Succ" [varN m], con "Zero" []],
                fun "acker" [varN m, con "Succ" [con "Zero"[]]])
              ,([m,n],[con "Succ" [varN m], con "Succ" [varN n]],
                fun "acker" [varN m,fun "acker" [con "Succ" [varN m],varN n]])
              ])
     ,NarR(toName "eqNat",
              [([],[con "Zero" [], con "Zero" []],con "True" [])
              ,([n],[con "Zero" [], con "Succ" [varN n]],con "False" [])
              ,([n],[con "Succ" [varN n], con "Zero" []],con "False" [])
              ,([n,m],[con "Succ" [varN n], con "Succ" [varN m]],fun "eqNat" [varN n,varN m])
              ])
    ,NarR(toName "half",
              [([],[con "Zero" []],con "Zero" [])
              ,([],[con "Succ" [con "Zero" []]],con "Zero" [])
              ,([n],[con "Succ" [con "Succ" [varN n]]],con "Succ" [fun "half" [varN n]])
              ])
    ,NarR(toName "lub",
             [([t],[total  ,varN t ],varN t)
             -- ,([t],[varN t ,total  ],varN t)
             ,([t],[partial,varN t ],partialT)
             -- ,([t],[varN t ,partial],partialT)
             ])
    ,NarR(toName "zap",
             [([a,t],[empty (varN a),varN t],con "Partial" [])
             ,([t],[univ,varN t],varN t)
             ,([x,y,t],[times (varN x) (varN y),varN t],zap (varN x) (zap (varN y) (varN t)))
             ,([x,y,t],[plus (varN x) (varN y),varN t],zap (varN x) (zap (varN y) (varN t)))
             ])
    ,NarR(toName "simp",
              [([],[univ],con "Univ" [])
              ,([a],[empty (varN a)],con "Empty" [varN a])
              ,([x,y],[times (varN x) (varN y)],simpT (simp (varN x)) (simp (varN y)))
              ,([x,y],[plus  (varN x) (varN y)],simpP(simp (varN x)) (simp (varN y)))
              ])
    ,NarR(toName "simpT",
               [([],[univ,univ],con "Univ" [])
               ,([x,y],[varN x,varN y],con "Times" [varN x,varN y])
               ])
    ,NarR(toName "simpP",
               [([],[univ,univ],con "Univ" [])
               ,([x,y],[varN x,varN y],con "Plus" [varN x,varN y])
               ])
    ,NarR(toName "union",
               [([y],[univ,varN y], con "Univ" [])
               ,([x],[varN x,univ], con "Univ" [])
               ,([a,y],[empty (varN a),varN y],varN y)
               ,([a,x],[varN x,empty (varN a)],varN x)
               ,([x,y,w,z],[times (varN x) (varN y),times (varN w) (varN z)],con "Times" [unionX (varN x)(varN w),unionX (varN y) (varN z)])
               ,([x,y,w,z],[plus (varN x) (varN y),plus (varN w) (varN z)],con "Plus" [unionX (varN x)(varN w),unionX (varN y) (varN z)])
               ])
    ,NarR(toName "app",
             [([ys],[con "Nil"[],varN ys], varN ys)
             ,([a,xs,ys],[con "Cons" [varN a, varN xs],varN ys],
                         con "Cons" [varN a,fun "app" [varN xs,varN ys]])
             ])
    ]
   where partial = con "Partial" []
         total = con "Total" []
         univ = con "Univ" []
         empty x = con "Empty" [x]
         times x y = con "Times" [x,y]
         plus x y = con "Plus" [x,y]
         partialT = con "Partial" []
         simpT x y = fun "simpT" [x,y]
         zap x y = fun "zap" [x,y]
         simp x = fun "simp" [x]
         simpP x y = fun "simpP" [x,y]
         unionX x y = fun "union" [x,y]

r1 :: NTerm z n v t => [Rule n v t]
r1 = (sampleRules fun con samples)
  where con s xs = injN(ConN (toName s) xs)
        fun s xs = injN(FunN (toName s) xs)


andT,takeT,ackT,eqNatT,halfT,lubT,zapT,appT:: NTerm z n v t => DefTree v t
andT = head (defTree (r1 !! 0))
takeT = head (defTree (r1 !! 1))
ackT = head (defTree (r1 !! 2))
eqNatT = head (defTree (r1 !! 3))
halfT = head (defTree (r1 !! 4))
lubT = head (defTree (r1 !! 5))
zapT = head (defTree (r1 !! 6))
appT = head (defTree (r1 !! 11))


treeOf s | (s == (toName "and")) = andT
treeOf s | (s == (toName "take")) = takeT
treeOf s | (s == (toName "acker")) = ackT
treeOf s | (s == (toName "eqNat")) = eqNatT
treeOf s | (s == (toName "half")) = halfT
treeOf s | (s == (toName "lub")) = lubT
treeOf s | (s == (toName "zap")) = zapT
treeOf s | (s == (toName "app")) = appT
treeOf s = error ("No def tree for: "++show s)

funF s xs = injN(FunN (toName s) xs)
conF s xs = injN(ConN (toName s) xs)

term1,term2,term2a,term3,term4,term5,term6 :: NTerm z n v t => t
term1 = funF "take" [varF 1,term2]
term2 = funF "app" [conF "Cons" [varF 2,conF "Nil" []],
                   conF "Cons" [varF 3,conF "Nil" []]]
term2a = conF "Cons" [varF 4,funF "app" [conF "Nil" [],conF "Cons" [varF 5,conF "Nil" []]]]
term3 = funF "take" [varF 6,term2a]
term4 = funF "lub" [varF 7,varF 7]
term5 = funF "take" [varF 8, funF "app" [conF "Cons" [varF 9,conF "Nil" []],varF 10]]
term6 = (eqf term5 (conF "Cons" [varF 11,conF "Cons" [varF 12,conF "Nil" []]]))

{-
testN :: NMonad z n v t m => t -> m [()]
testN x = (do { Answers ys <- narrow (20,100) [] [(x,[])]; mapM showP ys})
  where free = freeTerm x
        ok (var,term) = elem var free
        showP (term,un) = warnN [Ds "\n",dterm term,Ds "   where   "
                                ,++show (filter ok un)

-}