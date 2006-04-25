-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Tue Apr 25 12:54:27 Pacific Daylight Time 2006
-- Omega Interpreter: version 1.2.1

module NarrowMod {-(narrow,defTree,DefTree,Rule(..),NS(..),Un,
                  NTerm(..),NMonad(..),Speaks(..),
                  value, freeTerm, andf, eqf, sampleRules,conF, funF,
                  term1,term2a,term3,term4,term5,term6,testN
                 )-}    where

import List(union,find,partition)
import Auxillary(maybeM,plistf,plist)
import Monad(when)

data NS name var term
  = VarN var
  | FunN name [term]
  | ConN name [term]

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

class (Eq name,Show name,Eq var,Eq term,Show var,Show term) =>
      NTerm name var term |
      term -> var, term -> name, name -> term where
  projN :: term -> NS name var term
  injN :: NS name var term -> term
  varN :: var -> term
  subN :: Un var term -> term -> term
  mguN :: Monad m => [(term,term)] -> m(Un var term)
  matchN :: Monad m => Un var term -> [(term,term)] -> m(Un var term)
  success :: term
  equalName :: name
  andName :: name
  varWild :: var -> term
  termWild :: term -> term
  -- The next 3 are strictly for the sample definitions
  samples :: [(var,term)]
  toName :: String -> name
  varF :: Integer -> term

eqf x y = fun equalName [x,y]
andf x y = fun andName [x,y]
uneqf x = case projN x of
            ConN _ [a,b] -> (a,b)


class Monad m => Speaks m where
  speak :: String -> m ()
  delayN :: m Bool
  warnN :: m Bool
  forbidN:: m Bool
  showStepN:: m Bool

class (Speaks m,NTerm n v t) => NMonad n v t m where
  termFresh :: t -> m t
  varFresh :: v -> m t
  treeOfN :: n -> m(DefTree v t)
  treeOfN s = return(treeOf s)
  normN :: t -> m t

--------------------------------------------------------------
-- Show instances

instance (Show n,Show v,NTerm n v t) => Show (Rule n v t) where
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

freshX :: NMonad n v t m => ([v],t,t) -> m (t,t)
freshX (vs,ps,term) =
  do { ns <- mapM varFresh vs
     ; let subT = zip vs ns
     ; return(subN subT ps,subN subT term)}

fun n ys = injN(FunN n ys)
con n ys = injN(ConN n ys)

freshen :: (NMonad n v t m) => t -> m t
freshen x =
  case projN x of
   (VarN s) -> varFresh s
   (FunN n xs) -> do { ys <- mapM freshen xs; return(fun n ys)}
   (ConN n xs) -> do { ys <- mapM freshen xs; return(con n ys)}

liftN f x = f (projN x)

value :: (NTerm n v t) => t -> Bool
value x = liftN val x
 where val (VarN a) = True
       val (ConN s ts) = all value ts
       val (FunN s ts) = False

freeTerm :: NTerm n v t => t -> [v]
freeTerm x = liftN free x
  where free(VarN s) = [s]
        free(ConN t ts) = foldr (add freeTerm) [] ts
        free(FunN t ts) = foldr (add freeTerm) [] ts
        add freeF xs ys = union (freeF xs) ys

------------------------------------------------------
-- unifiers

-- composeUn :: Un v t -> Un v t -> Un v t
composeUn s1 s2 = ([(u,subN s1 t) | (u,t) <- s2] ++ s1)

subTwoList :: NTerm n v t => Un v t -> [(t,t)] -> [(t,t)]
subTwoList env xs = map f xs where f (x,y) = (subN env x,subN env y)

pushUnifier u1 [] = []
pushUnifier u1 ((exp,u2):xs) = (exp,composeUn u2 u1):pushUnifier u1 xs

----------------------------------------------------------------
-- Creating Definitional Trees

-- makeChainL (FunN "eq" [ConN "Zero"[],ConN "Zero"[]])
-- [Next {eq Zero Zero} [0] (Next {eq _ Zero} [1] (Root {eq _ _}))
-- ,Next {eq Zero Zero} [1] (Next {eq Zero _} [0] (Root {eq _ _}))
-- ]

makeChainL :: NTerm n v t => t -> [Chain v t]
makeChainL x = liftN h x
  where h (FunN name args) =
          do { zs <- generalizeL 0 args
             ; matchLx name args zs}

matchLx :: NTerm n v t => n -> [t] -> (Path,[t]) -> [Chain v t]
matchLx name args ([], newArgs) = return (Root (fun name newArgs))
matchLx name args (h:t, newArgs) =
  do { tail <- makeChainL (fun name newArgs)
     ; return (Next (fun name args) (h:t) tail)}


-- If we're computing a DefTree for {f a0 a1 a2 a3} then we call
-- generalizeL 0 [a0,a1,a2,a3]

generalizeL :: NTerm n v t => Int -> [t] -> [(Path,[t])]
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

renameVarN :: NTerm n v t => t -> t
renameVarN x = liftN h x
  where h (VarN vv) = varWild vv
        h (ConN name args) = con name (map renameVarN args)
        h (FunN name args) = fun name (map renameVarN args)

mainY :: NTerm n v t => n -> [([v],[t],t)] -> [DefTree v t]
mainY name patternList = do { zs <- mapM (f12 name) patternList
                            ; makeTreeL zs}
f12 name (free2,lhs,rhs) = map (makeTreePath free2 lhs2 rhs)
                               (makeChainL (renameVarN lhs2))
   where lhs2 = (fun name lhs)

defTree :: NTerm n v t => Rule n v t -> [DefTree v t]
defTree (NarR(name,zs)) = mainY name zs


------------------------------------------------------
-- operations on Paths

getPath :: NTerm n v t => [Int] -> t -> t
getPath [] x = x
getPath (n:ns) x = liftN h x
  where h (FunN nm ts) = getPath ns (ts !! n)
        h (ConN nm ts) = getPath ns (ts !! n)


firstFunN :: NTerm n v t => t  -> Maybe Path
firstFunN x = liftN h x
  where h(FunN _ _) = Just []
        h(VarN _) = Nothing
        h(ConN s ts) = get 0 (map firstFunN ts)
          where get n [] = Nothing
                get n ((Just path):ys) = Just(n:path)
                get n (Nothing : ys) = get (n+1) ys

insertAt 0 x (t:ts) = x:ts
insertAt n x (t:ts) = t : insertAt (n-1) x ts

subInPlace :: NTerm n v t => ((t,Un v t) -> c) -> Path -> t -> [(t,Un v t)] -> [c]
subInPlace k [] term subterms = map k subterms
subInPlace k (n:ns) x subterms = liftN h x
  where h (FunN name ts) = subInPlace k2 ns (ts !! n) subterms
            where k2 (x,u) = k((fun name (insertAt n x ts)),u)
        h (ConN name ts) = subInPlace k2 ns (ts !! n) subterms
            where k2 (x,u) = k((con name (insertAt n x ts)),u)

duplicateTerm :: NTerm n v t => Un v t -> Path -> t -> [(t,Un v t)] -> [(t,Un v t)]
duplicateTerm u path term subTs = pushUnifier u (subInPlace app path term subTs)
  where app (x,u) = (subN u x,u)

------------------------------------------------------------
-- narrowing

narrow :: (Eq t,NMonad n v t m) => Int -> [(t,Un v t)] -> m [(t,Un v t)]
narrow count xs | (count::Int) <= 0 = return []
narrow count [] = return []
narrow count ((x,u):xs) | value x =
   do { ys <- narrow (count - 1) xs; return ((x,u) : ys) }
narrow count ((x,u):xs) = liftN h x
  where h (FunN nm _) =
          do { verbose <- showStepN
             ; when verbose (speak ("\n"++show count++" narrowing1\n   "++show x++
                                    plist "\nothers\n   " (map fst xs) "\n   " "--\n"))
             ; (n,values,terms) <- oneStep x
             -- ; mapM (showStep "oneStep ") ys
             ; do { zs <- narrow (count - n) (xs ++ (pushUnifier u terms))
                  ; return(values++zs)
                  }}
        h _ = case firstFunN x of
               Just path ->
                 let exp = getPath path x
                 in do {  verbose <- showStepN
                       ; when verbose (speak (show count++" narrowing2 "++show x))
                       ; (n,values,exps) <- oneStep exp
                       ; let ys = duplicateTerm [] path x exps
                             vs = duplicateTerm [] path x values
                       ; do { zs <- narrow (count-n) (xs ++ (pushUnifier u ys))
                            ; return(vs++zs)}}
               Nothing -> do { ys <- narrow (count - 1) xs
                             ; return ((x,u) : ys) }

oneStep ::  (Eq t,NMonad n v t m) => t  -> m (Int,[(t,Un v t)],[(t,Un v t)])
oneStep x = do { all <- liftN h x
               ; let (vs,terms) = partition (\ (v,u) -> value v) all
               ; return(length vs,vs,terms)}
  where h (FunN nm [a,b]) | (nm == equalName) = eqStep x a b
        h (FunN nm _) = do { tree <- (treeOfN nm)
                           ; treeStep x tree }

eqStep :: (Eq t,NMonad n v t m) => t  -> t -> t -> m [(t,Un v t)]
eqStep x a b = do { delay <- delayN; h delay x (projN a) (projN b) }
  where h _ x (VarN s) (VarN t) =
          if  s==t then return[(success,[])]
                   else do { u <- mguN [(varN s,varN t)]; return[(success,u)]}
        h _ x (VarN s) (ConN nm ts) =
          do { vs <- mapM termFresh ts
             ; u <- mguN [(a,con nm vs)]
             ; return[(subN u x,u)]}
        h _ x (ConN nm ts) (VarN s) =
          do { vs <- mapM termFresh ts
             ; u <- mguN [(b,con nm vs)]
             ; return[(subN u x,u)]}
        h True x (VarN s) term@(FunN _ _) =
          do { t1 <- normN (injN term); u <- mguN [(varN s,t1)]; return[(success,u)]}
        h True x term@(FunN _ _) (VarN s) =
          do { t1 <- normN (injN term); u <- mguN [(varN s,t1)]; return[(success,u)]}
        h _ x (FunN _ _) (FunN _ _) | a==b = return[(success,[])]
        h _ x (FunN nm args) _ =
          do { (_,vs,ans) <- oneStep a
             ; return(duplicateTerm [] [0] x (vs++ans))}
        h _ x _ (FunN nm args) =
          do { (n,vs,ans) <- oneStep b
             ; return(duplicateTerm [] [1] x (vs++ans))}
        h _ x (t1@(ConN n xs)) (t2@(ConN m ys)) =
          if n==m
             then case mguN [(injN t1,injN t2)] of
                    Just env -> return[(success,env)]
                    Nothing -> case (xs,ys) of
                                ([],[]) -> return[(success,[])]
                                ([x],[y]) -> return[(eqf x y,[])]
                                (_,_) -> return[(foldr andf success (zipWith eqf xs ys),[])]
             else return[]


treeStep ::(Eq t,NMonad n v t m) => t -> DefTree v t -> m[(t,Un v t)]
treeStep t (Leaf pat free lhs rhs) = maybeM (matches t pat) ok (return [])
  where ok u3 = do { (lhs2,rhs2) <- freshX (free,lhs,rhs)
                   ; case matchN [] [(lhs2,t)] of
                       Just unifier -> return [(subN unifier rhs2,[])]
                         -- we're matching, so once applied to "rhs2",
                         -- the unifier is no longer useful, since it
                         -- binds no variables in "t". It is good to
                         -- match, rather than unify, since it avoids
                         -- introducing new variables some times. If
                         -- matching fails, we try unification.
                       Nothing -> case mguN [(lhs2,t)] of
                                    Just unifier -> return [(subN unifier rhs2,unifier)]
                                    Nothing -> return [] }
treeStep term (Branchx termX path ts) = maybeM (matches term termX) ok (return [])
  where ok (tm,u) =
         do { ws <- mapM (treeStep term) ts
            ; let new = (getPath path term)
            ; if all null ws
                 then case projN new of
                       (FunN nm _) ->
                          do { (n,vs,ans) <- (oneStep new)
                             ; return(duplicateTerm u path tm (vs++ans))}
                       _ -> case duplicateTerm u path tm [(new,[])] of
                             zs@[(new,un)] -> if term==new
                                                 then noProgress term
                                                 else return zs
                             zs -> return zs
                 else return(concat ws)}

noProgress term =
  fail ("While narrowing, the term:\n   "++show term++
        "\ndid not match any rule. The rules are probably incomplete.")

matches :: NMonad n v t m => t -> t -> m (Maybe (t,[(v,t)]))
matches term pat =
  do { p <- freshen pat;
     ; case mguN[(p,term)] of
         Nothing -> return Nothing
         Just u -> return(Just(subN u term,u))}

showStep :: NMonad n v t m => String -> (t,Un v t) -> m ()
showStep indent (x,u) = speak (indent++show x++"\n"++g (indent ++ "    ") u)
  where g i [] = ""
        g i ((v,t):xs) = (i++show v++" = "++show t++"\n")++(g i xs)


hnf :: NMonad n v t m => Un v t -> t -> m [(t,Un v t)]
hnf u x = liftN h x
  where h (VarN s) = return [(varN s,u)]
        h (FunN nm _) =
          do { (n,vs,ys) <- oneStep x
             ; let add [] = return []
                   add ((t,u2):ys) =
                      do { as <- hnf (composeUn u2 u) t
                         ; bs <- add ys
                         ; return(as++bs)}
             ; add (vs++ys)}
        h (ConN _ _) = return [(x,u)]

---------------------------------------------------------------
-- some sample rules, and a default treeOfN
-- These can be commented out, if desired

sampleRules :: NTerm n v t =>
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

r1 :: NTerm n v t => [Rule n v t]
r1 = (sampleRules fun con samples)
  where con s xs = injN(ConN (toName s) xs)
        fun s xs = injN(FunN (toName s) xs)


andT,takeT,ackT,eqNatT,halfT,lubT,zapT,appT:: NTerm n v t => DefTree v t
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

term1,term2,term2a,term3,term4,term5,term6 :: NTerm n v t => t
term1 = funF "take" [varF 1,term2]
term2 = funF "app" [conF "Cons" [varF 2,conF "Nil" []],
                   conF "Cons" [varF 3,conF "Nil" []]]
term2a = conF "Cons" [varF 4,funF "app" [conF "Nil" [],conF "Cons" [varF 5,conF "Nil" []]]]
term3 = funF "take" [varF 6,term2a]
term4 = funF "lub" [varF 7,varF 7]
term5 = funF "take" [varF 8, funF "app" [conF "Cons" [varF 9,conF "Nil" []],varF 10]]
term6 = (eqf term5 (conF "Cons" [varF 11,conF "Cons" [varF 12,conF "Nil" []]]))

testN :: NMonad n v t m => t -> m [()]
testN x = (do { ys <- narrow 20 [(x,[])]; mapM (speak . showP) ys})
  where free = freeTerm x
        ok (var,term) = elem var free
        showP (term,un) = "\n"++show term ++ "   where   "++show (filter ok un)

