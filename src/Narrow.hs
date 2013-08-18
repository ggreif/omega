{-# LANGUAGE FlexibleContexts
  , FlexibleInstances
  #-}

module Narrow(narr,defTree,Check(..),matches) where

import Data.List(union,find,partition)
import Auxillary(maybeM,plistf,plist,DispElem(..),displays
                ,Display(..),DispInfo,initDI)
import Control.Monad(when)
import Monads
import Bind(Name)
import RankN
import NarrowData
import Debug.Trace(trace)

class TyCh m => Check m where
  getMode :: String -> m Bool
  wait :: String -> m ()
  rewEq :: (Tau,Tau) -> m(Maybe Unifier2)
  rewNestedEqual :: (Tau,Tau) -> m (Maybe (Tau,Unifier2))
  getDefTree :: NName -> m(DefTree TcTv Tau)
  tryRewriting :: Tau -> m(Maybe (Tau,Unifier2))
  normalizeTau :: Tau -> m (Tau,Unifier2)


--------------------------------------------------
-- Unifiers and substitutions

subProb u (EqP(x,y)) = EqP(sub2Tau u x,sub2Tau u y)
subProb u (AndP rs) = AndP (map (subProb u) rs)
subProb u (TermP x) = TermP(sub2Tau u x)


pushUnifier u1 [] = []
pushUnifier u1 ((exp,u2):xs) = (exp,composeTwo u2 u1):pushUnifier u1 xs

--------------------------------------------------
-- Values, variables or a constructor applied to all values

valueP :: Prob Tau -> Bool
valueP (TermP t) = value t
valueP _ = False

liftN f x = f (project x)

value :: Tau -> Bool
value x = liftN val x
 where val (VarN a) = True
       val (ConN s ts) = all value ts
       val (FunN s ts) = False
       val (RelN x) = False

---------------------------------------------------------
-- operations on the threaded state of a narrowing computation
---------------------------------------------------------

decStep (nsteps,nsolution,disp,bool) = (nsteps - 1,nsolution,disp,bool)
decSol  (nsteps,nsolution,disp,bool) = (nsteps,nsolution - 1,disp,bool)
exceeded (nsteps,nsolution,disp,bool) = nsteps < 0
noMoreNeeded (nsteps,nsolution,disp,bool) = nsolution < 0
tooMany (nsteps,nsolution,disp,_) =  (nsteps,nsolution,disp,True)


------------------------------------------------------------
-- Tracing a narrowing computation

traceSteps (steps,count,d,exceeded) (problems@((ps,truths,us):_)) found =
  do { verbose <- getMode "narrowing"
     ; let f d (prob,truth,unifier@(ls,vs)) =
              displays d [Dd prob,if null vs
                                  then Ds "\n"
                                  else Dr[Ds " where ",dUn (ls,take 3 vs)]]
     ; d1 <- whenP verbose d
         [Ds "\n-------------------------------------\n"
         ,Ds (show steps), Ds " Narrowing the list (looking for "
         ,Ds (show count), Ds " solutions) found ",Ds (show (length found)),Ds "\n",Ds "   "
         ,Dlf f problems "\n   ",Ds "\nwith truths:\n   "
         ,dRel truths, Ds "\n"]
     ; when verbose (wait "narrowing")
     ; return (steps,count,d1,exceeded)
     }



traceResult (steps,count,d,exceeded) cntxt un =
  do { verbose <- getMode "narrowing"
     ; d1 <- whenP verbose d
              [Ds "\n*********************"
              ,Ds "\nFound a solution for:\n  ",Ds cntxt,Ds "\n  ",dUn un]
     ; return(steps,count,d1,exceeded)}

-------------------------------------------------------------------
-- The narrower itself

narr:: Check m => String -> ST Z -> Sol -> Sol -> m(Sol,ST Z)
narr cntxt s [] foundsols = return(reverse foundsols,s)
narr cntxt s problems foundsols | exceeded s = return(reverse foundsols,tooMany s)
narr cntxt s problems foundsols | noMoreNeeded s = return(reverse foundsols,s)
narr cntxt s ((t,ts,un):more) foundsols | valueP t =
  do { s1 <- traceResult s cntxt un
     ; narr cntxt (decSol s1) more (addSol (t,ts,un) foundsols)}
narr cntxt s (problems@((p,truths,u):more)) foundsols =
  do { s1 <- traceSteps s problems foundsols
     ; (newprobs,s2) <- stepProb s1 p truths
     ; narr cntxt (decStep s2) (more ++ map (push u) newprobs) foundsols }

--------------------------------------------------------
-- Taking 1 step in a narrowing computation

stepProb :: Check m => ST Z -> Prob Tau -> Rel Tau -> m(Sol,ST Z)
stepProb s (prob@(EqP(x,y))) truths =
  maybeM (rewNestedEqual (x,y))
         (\ (new,u1) -> do { truths2 <- subRels u1 truths
                           ; return([(TermP new,truths2,u1)],s)}) $
  maybeM (rewEq (x,y))
         (\ u1 -> do { truths2 <- subRels u1 truths
                     ; return([(TermP success,truths2,u1)],s)})
         (maybeM (truths `impliesM` (x,y))
                 (\ u1 -> do { verbose <- getMode "narrowing"
                             ; whenM verbose
                                 [Ds "\nWhile narrowing, the term:\n   "
                                 ,Dd prob, Ds "\nis implied by the truths, deriving ",dUn u1]
                             ; truths2 <- subRels u1 truths
                             ; return([(TermP success,truths2,u1)],s)})
                 (stepEq s (x,y) truths))


stepProb s (TermP t) truths = stepTerm s t truths
stepProb s (AndP []) truths = return([(TermP success,truths,([],[]))],s)
stepProb s (AndP [p]) truths = stepProb s p truths
stepProb (s@(nstep,nsol,d0,ex)) (AndP (p:ps)) truths =
  do { let (d1,cntxt) = displays d0 [Dd p]
           newS = (nstep,2,d1,False)
     ; (ans,s1@(nstep',_,d2,exceed)) <- narr ("And sub-problem\n  "++cntxt) newS [(p,truths,([],[]))] []
     ; if exceed
          then return ([],s1)
          else do { let nextS = (nstep'-1,nsol,d2,ex)
                  ; case ans of
                    [] -> return([],nextS)
                    [(TermP x,ts1,u1)] | x==success ->
                            return([(andP(map (subProb u1) ps),ts1,u1)],nextS)
                    new -> let add (p,ts,u1) = (andP(map (subProb u1) ps++[p]),ts,u1)
                           in return(map add new,nextS)}}

stepEq:: Check m => ST Z -> (Tau,Tau) -> Rel Tau -> m(Sol,ST Z)
stepEq s0 (a,b) truths =
 case (project a,project b) of
  (VarN x,VarN y) | x==y -> return([(TermP success,truths,([],[]))],s0)
  (VarN x,VarN y) ->
    do { (u,s1) <- mguV s0 truths [(TcTv x,TcTv y)]
       ; truths2 <- subRels u truths
       ; return([(TermP success,truths2,u)],s1)}
  (VarN s,ConN nm ts) | (properSubTerm s b) -> return ([],s0)
  (ConN nm ts,VarN s) | (properSubTerm s a) -> return ([],s0)
  (VarN s,ConN nm ts) ->
    do { vs <- mapM termFresh ts
       ; (u,s1) <- mguV s0 truths [(a,con nm vs)]
       ; truths2 <- subRels u truths
       ; return([(EqP (sub2Tau u a,sub2Tau u b),truths2,u)],s1)}
  (ConN nm ts,VarN s) ->
    do { vs <- mapM termFresh ts
       ; (u,s1) <- mguV s0 truths [(b,con nm vs)]
       ; truths2 <- subRels u truths
       ; return([(EqP (sub2Tau u a,sub2Tau u b),truths2,u)],s1)}
  (FunN _ _,FunN _ _) | a==b -> return([(TermP success,truths,([],[]))],s0)

  (FunN nm args,FunN nm2 args2) ->
    handleM 4
    (do { (ansA,s1) <- stepTerm s0 a truths
        ; (ansB,s2) <- stepTerm s1 b truths
        -- we are only going to pursue one path, so choose one
        ; case fewestVar ansA a ansB b of
           (bool,ans,term) -> return(map (buildQ bool term) ans,s2)})
    (\ s -> if nm /= nm2
               then failM 3 [Ds s]
               else
                 do { ans <- mguB (zip args args2)
                    ; case ans of
                       Right (m,x,y) -> failM 3 [Ds s]
                       Left u -> do { ts <- subRels u truths
                                    ; return([(TermP success,ts,u)],s0)}})
  (FunN nm args, rhs) ->
    handleM 4 (do { (ans,s1) <- stepTerm s0 a truths
                  ; return(map (buildQ True b) ans,s1)})
              (failEq s0 truths a rhs)
  (lhs,FunN nm args) ->
    handleM 4 (do { (ans,s1) <- stepTerm s0 b truths
                  ; return(map (buildQ False a) ans,s1)})
              (failEq s0 truths b lhs)
  (ConN n xs,ConN m ys) | n /= m -> return([],s0)
  (ConN _ xs,ConN _ ys) | xs == ys -> return([(TermP success,truths,([],[]))],s0)
  (t1@(ConN n xs),t2@(ConN m ys)) | n==m ->
    case (xs,ys) of
     ([],[]) -> return([(TermP success,truths,([],[]))],s0)
     ([x],[y]) -> return([(EqP(x,y),truths,([],[]))],s0)
     (_,_) -> return([(andP(zipWith (curry EqP) xs ys),truths,([],[]))],s0)


failEq :: Check m => ST Z -> Rel Tau -> Tau -> NS NName TcTv Tau -> String -> m(Sol,ST Z)
failEq s0 truths fun (VarN s) mess =
  do { (u,s1) <- mguV s0 truths [(TcTv s,fun)]
     ; truths2 <- subRels u truths
     ; return([(TermP success,truths2,u)],s1)}
failEq s0 truths fun other mess =
  failM 3 [Ds  "\nWhile narrowing the equality:\n   ",Dd (eqf fun (inject other)),Ds mess]


stepTerm:: Check m => ST Z -> Tau -> Rel Tau -> m(Sol,ST Z)
stepTerm s0 term truths =
  case project term of
   (VarN _) -> return([(TermP term,truths,([],[]))],s0)
               -- VarN case Should be unreachable, if the valueP test works.
   (FunN nm _) -> maybeM
                   (tryRewriting term)
                   (\ (t,u) -> do { truths2 <- subRels u truths
                                  ; return([(TermP t,truths2,u)],s0)})
                   (do { tree <- getDefTree nm
                       ; stepTree nm term truths tree s0})
   (ConN _ _) -> case pathTo1stFunN term of
                  Just path ->
                    do { let exp = getTermAtPath path term
                       ; (ans,s1) <- stepTerm s0 exp truths
                       ; return(map (reBuild term path) ans,s1)}
                  Nothing -> return([(TermP term,truths,([],[]))],s0)
   (RelN (EqR(x,y))) -> do { ans <- stepProb s0 (EqP(x,y)) truths
                           ; return ans}

reBuild term path (TermP x,ts,u) = (problem,ts,u)
    where problem = TermP(sub2Tau u (insertNewTermAtPath term path x))


stepTree:: Check m => NName ->  Tau -> Rel Tau -> DefTree TcTv Tau -> ST Z -> m(Sol,ST Z)
stepTree name t truths (Leaf pat free lhs rhs) s0 =
   maybeM (matches t pat)                             -- test
          (applyLfRule s0 t truths (free,lhs,rhs))    -- if successful
          (return ([],s0))                            -- if failure
stepTree name term truths (Branchx termX path ts) s0 =
   maybeM (matches term termX)
          (applyBranchRule s0 name term truths (path,ts))
          (return ([],s0))

-- When applying a Branchx rule, find the deepest rules that match, and
-- use their answers. If there are any. Note, that there may be more than
-- one subtree that matches, if so, combine all the answers. If no
-- subtree matches, then use the root, and narrow the subterm pointed
-- to by path. Get multiple answers, by rebuilding the term, once for
-- for each answer for the subterm pointed to by path.

applyBranchRule :: Check m => ST Z -> NName -> Tau -> Rel Tau ->
   (Path,[DefTree TcTv Tau]) ->
   (Tau,([(TcLv,Level)],[(TcTv,Tau)])) ->
   m (Sol,ST Z)
applyBranchRule s0 name term truths (path,subtrees) (matched,mU) =
  do { (ansListList,s1) <- mapThread s0 (stepTree name term truths) subtrees
     ; let new = getTermAtPath path term
     ; case all null ansListList of
        False -> return(concat ansListList,s1) -- At least 1 answer: use them
        True -> case project new of -- No subtree applies so use root
                 (FunN nm _) ->
                     do { (ans,s2) <- stepTerm s1 new truths
                        ; return(map (reBuild term path) ans,s2)}
                 other -> let newest = insertNewTermAtPath matched path new
                          in if newest==term
                                 then maybeM (tryRewriting term)
                                             (\(t2,u2) -> return([(TermP t2,truths,composeTwo u2  mU)],s1))
                                             (noProgress name term)
                                 else do { truths2 <- subRels mU truths
                                         ; return ([(TermP newest,truths2,mU)],s1)}}

noProgress:: Check m => NName -> Tau -> m a
noProgress name term =
  failM 1
        [Ds "\nNo progress can be made on the term:\n   ",Dd term
        ,Ds ("\nNo rule for "++show name++" matched.\nEither the rules are incomplete, or a lemma is needed.")]



-- In applyLfRule, We first match the term against lhs,
-- recall match [(lhs,term)] only binds variables in lhs, so if
-- this succeeds, the unifier is only useful to apply to "rhs2".
-- It mentions no variables in "term" or "truths" since the vars
-- in "lhs2" are fresh. It is good to match, rather than unify,
-- since it avoids introducing new variables some times. If
-- matching fails, we try unification.

applyLfRule s0 term truths rule uselessUnifier =
  do { (lhs2,rhs2) <- freshX rule
     ; case match2 ([],[]) [(lhs2,term)] of
         Just unifier ->
           return ([(TermP(sub2Tau unifier rhs2),truths,([],[]))],s0)
         Nothing ->
           do { ans <- mguB [(lhs2,term)]
              ; case ans of
                 Left(ls,u2) ->
                    let important = freeTerm term
                        u3 = orientBindings important u2
                        good (var,term) = elem var important
                    in do { truths2 <- subRels (ls,u3) truths
                          ; return ([(TermP(sub2Tau (ls,u3) rhs2),truths2,(ls,filter good u3))],s0)}
                 Right _ -> return ([],s0) }}

----------------------------------------------------------------
-- Helper functions

-- A unifier, u1, is more general than another unifier, u2, iff
-- every binding in u1 appears in u2. For example [p=a] is more
-- general than [b=#0, p=a] and also more general than [b=#(1+c), p=a]
-- moreGen :: NTerm z n v t => Un v t -> Un v t -> Bool

moreGen [] u2 = True
moreGen (p:ps) u2 = elem p u2 && moreGen ps u2

-- Add a solution, only every previous solution is not more general
addSol n@(t,ts,(new1,new2)) us =
   if (all (\ (t,ts,(old1,old2)) -> not(moreGen old2 new2) && not(moreGen old1 new1)) us)
      then n:(filter (\ (t,ts,(old1,old2)) -> not(moreGen new2 old2) && not(moreGen new1 old1)) us)
      else us

push u (prob,truths,u2) = (prob,truths,composeTwo u2 u)

impliesM :: Check m => Rel Tau -> (Tau,Tau) -> m(Maybe Unifier2)
impliesM (EqR(a,b)) (x,y) =
   maybeM (mostGenUnify [(x,a),(y,b)])
          (\ u -> return(Just u))
          (maybeM (mostGenUnify [(x,b),(y,a)])
                  (\ u -> return (Just u))
                  (return Nothing))
impliesM (AndR []) (x,y) = return Nothing
impliesM (AndR (r:rs)) (x,y) =
  maybeM (impliesM r (x,y))
         (\ u -> return(Just u))
         (impliesM (AndR rs) (x,y))



subRels u (EqR(x,y)) =
  do { (a,u1) <- normalizeTau(sub2Tau u x)
     ; (b,u2) <- normalizeTau(sub2Tau u1 y)
     ; ans <- simpRel(EqR(a,b))
     ; return ans}
subRels u (AndR rs) = do { ans <- mapM (subRels u) rs; return(AndR ans)}

simpRel (EqR(x,y)) =
  do { ans <- handleM 5 (stepEq (10,2,initDI,False) (x,y) (AndR []))
                        (\ s -> return([],(0,0,undefined,True)))
                        -- Return an 'other' case if a failure occurs
     ; case ans of
        ([(EqP(a,b),_,([],[]))],(_,_,_,False)) -> simpRel (EqR(a,b))
        other -> return(EqR(x,y))
     }

-- If narrowing (Eq v (Con 2 v)) where v is a subterm
-- of a Constructor which is not nested inside a function
-- (i.e. something like (Eq v (Con {plus v 4} 2)) might be ok.)
-- then the narrowing must fail, as no terms are infinite.

properSubTerm :: TcTv -> Tau -> Bool
properSubTerm v x = liftN free x
  where free(VarN s) = s==v
        free(ConN t ts) = any (properSubTerm v) ts
        free(FunN t ts) = False
        free(RelN x) = False

fewestVar xAns xterm yAns yterm =
     if xn <= yn then (True,xAns,yterm) else (False,yAns,xterm)
  where count (term,truths,(ls,unifier)) = length unifier
        xn = sum(map count xAns)
        yn = sum(map count yAns)

varsOf xs = foldr acc ([],[],[]) (map f xs)
  where acc (a,b,c) (as,bs,cs) = (a++as,b++bs,c++cs)
        f (x,y) = let (a,b,c) = varsOfTau x
                      (m,n,p) = varsOfTau y
                  in (a++m,b++n,c++p)

varsOfRel f (EqR (x,y)) = union3 (f x) (f y)
varsOfRel f (AndR []) = ([],[],[])
varsOfRef f (AndR (r:rs)) = union3 (varsOfRel f r) (varsOfRel f (AndR rs))

mguV :: Check m => ST Z -> Rel Tau -> [(Tau,Tau)] -> m(Unifier2,ST Z)
mguV s0 truths pairs =
  do { maybe <- mguB pairs
     ; case maybe of
        Left u2 -> return(u2,s0)
        Right ("Rigid",v,t) ->
            (do { (descrip,loc) <- locInfo v
                ; ms <- case t of
                         (TcTv(Tv n (Rigid _ _ _) _)) ->
                            do { (name2,loc2) <- locInfo t
                               ; return [Ds "\nThe var ", Dd t
                                        ,Ds " arose from ", Ds name2
                                        ,Ds ("\nnear "++ loc2)
                                        ,Ds ("\n " ++shtt v++" =/= "++shtt t)]}
                         other -> return []
                ; failM 3 [Ds "The supposedly polymorphic type variable: ",Dd v
                          ,Ds ",\nis forced by context to be: ", Dd t
                          ,Ds "\nThe var ",Dd v,Ds " arose from "
                          ,Ds descrip
                          ,Dr ms]})
        Right (s,t1,t2) ->
          -- showKinds varsOf pairs >>
          -- showKinds (varsOfRel varsOfTau) truths >>
          -- warnM [Ds "\nPairs = ", Dl pairs ","] >>
          -- warnM [Ds "\nt1 = ",Dd t1,Ds " t2 = ",Dd t2,Ds "\n truths =",Dd truths] >>
          fail ("Unification of (var,term) failed, this should be impossible\n "++s++" "++shtt t1++" /= "++shtt t2)
     }


locInfo (TcTv (Tv un (Rigid q loc (nm,ref)) k)) =
  do { t <- readRef ref; x <- fromIO t; return(x,show loc)}
locInfo _ = return ("?","unknown")

-- True means put the problem on left, False means on right
buildQ True  y (TermP x,ts,u) = (EqP(x,sub2Tau u y),ts,u)
buildQ False y (TermP x,ts,u) = (EqP(sub2Tau u y,x),ts,u)
buildQ _ _ prob = error ("Non term problem returned from stepTerm in equality")



matches :: Check m => Tau -> Tau -> m (Maybe (Tau,Unifier2))
matches term pat =
  do { p <- freshen pat;
     ; maybeM (mostGenUnify [(p,term)])
              (\ u -> return(Just(sub2Tau u term,u)))
              (return Nothing)}


orientBindings free [] = []
orientBindings free ((p@(var,term)):more) =
  let rest = orientBindings free more
  in case project term of
      VarN nm -> if elem var free
                    then (nm,TcTv var):rest
                    else p:rest
      _ -> p:rest

freeTerm :: Tau -> [TcTv]
freeTerm x = liftN free x
  where free(VarN s) = [s]
        free(ConN t ts) = foldr (add freeTerm) [] ts
        free(FunN t ts) = foldr (add freeTerm) [] ts
        free (RelN (EqR(x,y))) = union (freeTerm x) (freeTerm y)
        add freeF xs ys = union (freeF xs) ys

occursN::TcTv -> Tau -> Bool
occursN v t = elem v (freeTerm t)


mapThread d0 f [] = return([],d0)
mapThread d0 f (x:xs) =
  do { (y,d1) <- f x d0
     ; (ys,d2) <- mapThread d1 f xs
     ; return(y:ys,d2)}

------------------------------------------------------
-- operations on Paths

getTermAtPath :: Path -> Tau -> Tau
getTermAtPath [] x = x
getTermAtPath (n:ns) x = liftN h x
  where h (FunN nm ts) = getTermAtPath ns (ts !! n)
        h (ConN nm ts) = getTermAtPath ns (ts !! n)
        h (RelN (EqR (x,y))) = getTermAtPath ns ([x,y] !! n)

insertNewTermAtPath old [] new = new
insertNewTermAtPath old (path@(n:ns)) new =
  case project old of
    FunN name ts -> fun name (insertAt n (insertNewTermAtPath (ts !! n) ns new) ts)
    ConN name ts -> con name (insertAt n (insertNewTermAtPath (ts !! n) ns new) ts)
    RelN (EqR(t0,t1)) -> let ts = [t0,t1]
                         in eq (insertAt n (insertNewTermAtPath (ts !! n) ns new) ts)


pathTo1stFunN :: Tau  -> Maybe Path
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

subInPlace :: ((Tau,Unifier2) -> c) -> Path -> Tau -> [(Tau,Unifier2)] -> [c]
subInPlace k [] term subterms = map k subterms
subInPlace k (n:ns) x subterms = liftN h x
  where h (FunN name ts) = subInPlace k2 ns (ts !! n) subterms
            where k2 (x,u) = k((fun name (insertAt n x ts)),u)
        h (ConN name ts) = subInPlace k2 ns (ts !! n) subterms
            where k2 (x,u) = k((con name (insertAt n x ts)),u)
        h (RelN (EqR(term1,term2))) = subInPlace k2 ns ([term1,term2] !! n) subterms
            where k2 (x,u) = k((eq (insertAt n x [term1,term2])),u)

duplicateTerm :: Unifier2 -> Path -> Tau -> [(Tau,Unifier2)] -> [(Tau,Unifier2)]
duplicateTerm u path term subTs = pushUnifier u (subInPlace app path term subTs)
  where app (x,u) = (sub2Tau u x,u)


----------------------------------------------------------------
-- Creating Definitional Trees

-- makeChainL (FunN "eq" [ConN "Zero"[],ConN "Zero"[]])
-- [Next {eq Zero Zero} [0] (Next {eq _ Zero} [1] (Root {eq _ _}))
-- ,Next {eq Zero Zero} [1] (Next {eq Zero _} [0] (Root {eq _ _}))
-- ]



makeChainLM :: Check m => Tau -> m[Chain TcTv Tau]
makeChainLM x = liftN h x
  where h (FunN name args) =
          do { pairs <- generalizeLM 0 args
             ; ans <- mapM (matchLXM name args) pairs
             ; return(concat ans)}


-- If we're computing a DefTree for {f a0 a1 a2 a3} then we call
-- generalizeL 0 [a0,a1,a2,a3]


matchLXM :: Check m => NName -> [Tau] -> (Path,[Tau]) -> m [Chain TcTv Tau]
matchLXM name args ([], newArgs) = return [(Root (fun name newArgs))]
matchLXM name args (h:t, newArgs) =
  do { tails <- makeChainLM (fun name newArgs)
     ; return(map (Next (fun name args) (h:t)) tails)}




generalizeLM :: Check m => Int -> [Tau] -> m[(Path,[Tau])]
generalizeLM _ [] = return [([],[])]
generalizeLM n (arg_n : args) = liftN h arg_n
  where h (VarN vv) =
          do { newTerm <- return(varWild vv)
             ; pairs <- generalizeLM (n+1) args
             ; return(do { (newPos, newRest) <- pairs
                         ; return (newPos, newTerm : newRest)})}
        h (ConN name ts) =
          do { pairs <- generalizeLM 0 ts
             ; pairs2 <- generalizeLM (n+1) args
             ; pairs3 <- mapM matchM pairs
             ; return(pairs3 ++ foldr add [] pairs2)}
          where matchM ([], _) = do { ans <- termWildM arg_n; return([n], ans : args)}
                matchM (a:b, newArgs) = return(n:a:b, con name newArgs : args)
                add (a:b, newRest) ans = (a:b, con name ts : newRest):ans
                add ([], newRest) ans = ans
        h f@(FunN _ _) = failM 3 [Ds "Type function call in pattern? ", Dd f]
        h r@(RelN _) = failM 3 [Ds "Relation in pattern? ", Dd r]


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

makeTreeL :: [DefTree TcTv Tau] -> [DefTree TcTv Tau]
makeTreeL leaf@[Leaf x free lhs rhs] = leaf
makeTreeL (Branchx term pos tree : rest)
  | all branchP rest &&
    all (== pos) (map (\(Branchx _ p _) -> p) rest)
  = do { zs <- mapM makeTreeL (partition children)
       ; return( Branchx term pos zs)}
  where children = concat (map (\(Branchx _ _ t) -> t)
                               (Branchx term pos tree : rest))
        partition [] = []
        partition (leaf@(Leaf x free lhs rhs) : rest) = [leaf] : partition rest
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

renameVarN :: Tau -> Tau
renameVarN x = liftN h x
  where h (VarN vv) = varWild vv
        h (ConN name args) = con name (map renameVarN args)
        h (FunN name args) = fun name (map renameVarN args)
        h (RelN (EqR(x,y))) = eq [renameVarN x, renameVarN y]


fff xs = plistf ff "[1" xs "\n" "1]"
  where ff y = plistf tree2string "[2" y "\n" "2]"

mainYM :: Check m => NName -> [([TcTv],[Tau],Tau)] -> m[DefTree TcTv Tau]
mainYM name patternList = do { pairs <- mapM (f13 name) patternList
                             ; let allPossibleOneFromEach = cross2 pairs
                             ; return(concat(map makeTreeL allPossibleOneFromEach))}

  where f13:: Check m => NName -> ([TcTv],[Tau],Tau) -> m [DefTree TcTv Tau]
        f13 name (free2,lhs,rhs) = do { pairs <- makeChainLM (renameVarN lhs2);
                                      ; return(map (makeTreePath free2 lhs2 rhs) pairs)}
                where lhs2 = fun name lhs


defTree :: Check m => Rule NName TcTv Tau -> m[DefTree TcTv Tau]
defTree (NarR(name,zs)) = mainYM name zs


cross2 []  = []
cross2 [xs] = map (\x->[x]) xs
cross2 (xs:xss) = [ x:ys   | x <- xs, ys <- cross2 xss ]




--------------------------------------------------------------
-- Show instances

----------------------------------------------
-- Helper function for making Display elements

dUn :: Unifier2 -> DispElem Z
dUn (_,xs) = Dlf (\ d (v,t) -> displays d [Dd v, Ds "=", Dd t]) xs ", "


instance Show (Rule NName TcTv Tau) where
  show (NarR(nm,xs)) =  "\n"++plistf f "" xs "\n" ""
    where f (vs,xs,t) = plistf show "[" vs "," "]"++"{"++show nm++" "++plistf h "" xs " " ""++"} = "++show t
          h x | conP x = "("++show x++")"
          h a = show a
          conP x = case (project x) of { ConN _ (z:zs) -> True; _ -> False}


tree2string tree = indent 0 tree
  where indent n (Leaf term free lhs rhs ) = blanks n ++ "Leaf " -- ++ (show term) ++  ",   "
                                            ++ show lhs ++ " --> "++show rhs
        indent n (Branchx term pos tree) = blanks n ++
          "Branchx " ++ (show pos) ++ " " ++ (show term) ++
          concat (map (\x -> indent (n+1) x) tree)
        blanks n = "\n" ++ (take n (repeat ' '))


----------------------------------------------------------------
