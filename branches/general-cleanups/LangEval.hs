-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Thu Nov  8 15:51:28 Pacific Standard Time 2007
-- Omega Interpreter: version 1.4.2

module LangEval where

import Auxillary
import Syntax
import Encoding2
import Monad(foldM)
import Monads(Exception(..), FIO(..),unFIO,handle,runFIO,fixFIO,fio,
              write,writeln,HasNext(..),HasOutput(..))
import Value
import RankN --(Sigma,runType,liftType, sigma4Eq,sigma4Hide,ToEnv,
             -- star,star_star,poly,intT)
import RankN(Z)
import Char(chr,ord)

import ParserDef(pe)
import System.IO.Unsafe(unsafePerformIO)
import List(union,unionBy,(\\),find)
import Bind
import PrimParser (parserPairs)
import SyntaxExt(Extension(..),SynExt(..))


type Level = Int

type Env = Ev

-------------------------------
-- Gensym

data Prefix = None | Tick | First

gensym :: HasNext m => Prefix -> Var -> m Var
gensym None s = return s
gensym p (Global s) = do { n <- nextInteger
                         ; return(Global (prefix p s ++ '`' : show n)) }
  where prefix First (s:ss) = [s]
        prefix First [] = "x"
        prefix Tick cs = takeWhile (/= '`') cs
gensym p (Alpha s _) = error "No gensym for Alpha yet"

genSym :: HasNext m => Var -> m Var
genSym = gensym Tick

-----------------------------------------------------------------------
-- Operations on runtime environments Ev

empty = Ev [] (unit,bind,fail)
  where (Vcon (Global "Monad",oX) [unit,bind,fail]) = maybeMonad

app (Ev xs m) (Ev as _) = Ev (xs ++ as) m

static :: Var -> Ev -> Maybe V
static s (Ev xs m) = lookup s xs

enames (Ev xs m) = map fst xs

extendV :: EnvFrag -> Env -> Env
extendV fs (Ev xs m) = Ev (fs ++ xs) m

extract :: String -> [ Var ] -> Env -> Env
extract term free (env@(Ev xs m)) = Ev statBound m
  where statBound = map find free
        find nm = case lookup nm xs of
                    Nothing ->
                      error ("Name not found in extract: "++ show nm++
                             "\n "++term++"\n "++show (map fst xs))
                    Just v -> (nm,v)


---------------------------------------------------------------
--- Extract parts of the current monad from the environment

monadUnit (Ev _ (unit,bind,fail)) = unit
monadBind (Ev _ (unit,bind,fail)) = bind
monadFail (Ev _ (unit,bind,fail)) = fail


-- The do syntax uses a monad stored in the run-time environment. The default
-- monad is Maybe. This code precomputes a value which is the default maybeMonad
maybeMonad = unsafePerformIO (runFIO action (\ loc n s -> error s)) where
  Right(bind,_)= pe "\\ x g -> case x of {Nothing -> Nothing; Just x -> g x}"
  Right(unit,_) = pe "Just"
  Right(fail,_) = pe "\\ x -> Nothing"
  action = do { b <- eval env0 bind
              ; u <- eval env0 unit
              ; f <- eval env0 fail
              ; return(Vcon (Global "Monad",Ox) [u,b,f])}


------------------------------------------------------------------------

getFreeTermVars bound term = free(vars bound term emptyF)
{-
filter p (expFV bound term)
  where -- The dependency checker introduces names with prefixes '%' and '::' which
        -- are used by the type checker, but don't really exist, so we have to
        -- filter them out
        p (Global ('%':_)) = False
        p (Global (':' : ':' : _)) = False
        p _ = True
-}
-----------------------------------------------------

evalVar env s =
  case static s env of
    Nothing -> fail ("Unknown Var at level 0: "++ show s)
    Just v -> return v

eval env@(Ev xs m) x =
   do { -- writeln(">> "++show x ++ " with " ++ show (map fst (take 6 xs)));
        ans <- evalZ env x
      -- ; writeln("<< "++show ans)
      ; return ans }

evalZ ::  Env -> Exp -> FIO V
evalZ env (Var s) = evalVar env s
evalZ env (Lit (ChrSeq s)) = return(VChrSeq s)
evalZ env (Lit (CrossStage v)) = return v
evalZ env (Lit x) = return(Vlit x)
evalZ env (Sum inj x) = do { v <- eval env x; return(Vsum inj v) }
evalZ env (Prod x y) =
    do { a <- eval env x; b <- eval env y; return(Vprod a b) }
evalZ env (CheckT x) = eval env x
evalZ env (Lazy x) = vlazy (eval env x)
evalZ env (Exists x) = eval env x
evalZ env (Under p x) = eval env x
evalZ env exp@(App f x) =
  do { g <- eval env f
     ; y <- eval env x
     ; applyV (show exp) g y }
evalZ env (Lam ps body xs) = return(makeLam ps body [] [] env)

evalZ env (Case x ms) = do { v <- eval env x; caseV ms env v ms }
  where caseV ms env v [] = caseErr v (map (\(loc,p,b,ds)->p) ms)
        caseV ms env v ((loc,p,body,ds):ps) =
          do { z <- matchStrict Tick p v env
             ; case z of
                Nothing -> caseV ms env v ps
                Just es ->
                  do { let env1 = (extendV es env)
                     ; env2 <- elaborate Tick ds env1
                     ; evalBody env2 body (caseV ms env v ps) } }
        caseErr v ps = fail("\nCase match failure\nThe value: "++show v++"\ndoesn't match any of the patterns:\n  "++
                        plist "" ps "\n  " "\n"++(pv v))
evalZ env (Let ds e) = do { env' <- elaborate Tick ds env; eval env' e }
evalZ env (Do stmts) =
  do { bind <- evalVar env (Global "bind") -- (monadBind env)
     ; fail <- evalVar env (Global "fail") -- (monadFail env)
     ; evalDo bind fail stmts env }
evalZ env (Bracket e) =
  do { e2 <- freshE e
     ; e3 <- rebuild 1 env e2
     ; return (Vcode e3 empty) }
evalZ env (Escape e) = fail ("Escape not allowed at level 0" ++ (show (Escape e))) --evalZ env e
evalZ env (Run e) =
  do { x <- eval env e
     ; case x of
        Vcode c env2 -> eval env2 c
        v -> fail ("Run expression:\n  "++show (Run e)++
                   "\nDoes not evaluate to code:\n   "++show v)
     }

evalZ env (Reify s v) = return(push env v)
evalZ env (Ann x t) = eval env x
evalZ env e = fail ("\n\nNo such exp yet: "++show e)


-- "rebuild" is an almost generic walk over a term. We build a (Par m)
--  to indicate where its not generic.

rebuild level env e = parE e (makeR env 1 [])

makeR env level perm = Par ext app inc esc
  where ext (Global s) = return(Global s,makeR env level perm)
        ext (Alpha s n) =
            do { n' <- fresh
               ; return(Alpha s n',makeR env level ((n,n'):perm)) }
        app v = let name = swaps perm v
                in case static name env of
                    Just v -> return(Reify (show name) v)
                    Nothing -> return(Var name)
        inc = makeR env (level+1) perm
        esc e = case level of
                 0 -> fail "Escape at level 0"
                 1 -> do { ww <- eval env (swaps perm e)
                         ; let unCode (Vcode x _) = return x
                               unCode other = fail ("\nNon code returned by ~("++show e++")\n with value: "++show other)
                         ; analyzeWith unCode ww
                         }
                 2 -> do { x <- parE e (makeR env (level - 1) perm)
                         ; return(Escape x) }

-- To make a Vf object we have to build a bunch of functions that "self swap"
-- and "self push" the Vf object built.

makeLam ps body frag perm1 env = Vf (f frag ps) push swapp
  where push env2 = makeLam ps body frag perm1 (app env env2)
        swapp perm2 = makeLam ps body frag (perm2 ++ perm1) env
        f frag (p:ps) v =
           do { --outputString ("In Vf with: "++show v);
                z <- mPatStrict Tick frag p v
              ; case (z,ps) of
                 (Just frag2,[]) -> eval (extendV frag2 (swaps perm1 env)) body
                 (Just frag2,ps) -> return(makeLam ps body frag2 perm1 env)
                 (Nothing,_) -> fail ("Pattern: "++show p++" does not match: "++show v++"\n")}



----------------------------------------------------------------------------
-- The semantic functions that implement the Maybe monad. Translates
-- do { p <- x; cont }  TO
-- bind x (\ z -> case z of { p -> cont; _ -> fail "matcherr"})

evalBind :: Env -> V -> V -> Pat -> V -> (Env -> FIO V) -> FIO V
evalBind env bind fail p x cont =
    do { g <- applyV badBind bind x
       ; applyV badBind2 g (Vprimfun "implicit case in pat bind of Do exp" casef) }
  where badBind = "Inside Do, the local definition for 'bind' is not a function"
        badBind2 ="Inside Do, the local definition for 'bind', " ++
                  "does not return a function when applied"
        badFail = "Inside Do, the local definition for 'fail' is not a function"
        message v = to ("Match Error in do binding: "++show p++" /= "++show v)
        casef v = do { z <- matchStrict Tick p v env
                     ; case z of
                         Nothing -> applyV badFail fail (message v)
                         Just es -> cont (extendV es env)}

evalDo :: V -> V -> [Stmt Pat Exp Dec] -> Ev -> FIO V
evalDo bind fail [ NoBindSt loc e ] env = eval env e
evalDo bind _ [ e ] env =
   fail ("The last Stmt in a do-exp must be simple: "++(show e))
evalDo bind fail ((BindSt loc p e):ss) env =
   do { ev <- eval env e
      ; evalBind env bind fail p ev (evalDo bind fail ss)}
evalDo bind fail ((NoBindSt loc e):ss) env =
   do { ev <- eval env e
      ; evalBind env bind fail Pwild ev (evalDo bind fail ss)}
evalDo bind fail ((LetSt loc ds):ss) env =
   do {env2 <- elaborate Tick ds env; evalDo bind fail ss env2 }

--------------------------------------------------------

evalBody :: Env -> Body Exp -> FIO V -> FIO V
evalBody env (Normal e) failcase = eval env e
evalBody env (Guarded xs) failcase = test env xs
 where test env [] = failcase
       test env ((x,y):xs) = ifV (eval env x) (eval env y) (test env xs)
evalBody env Unreachable failcase = fail "Impossible! Execution of Unreachable code."

px x = putStrLn x

ifV :: Monad a => a V -> a b -> a b -> a b
ifV x y z =
  do { b <- x
     ; case b of
         Vcon (Global "True",_) [] -> y
         Vcon (Global "False",_) [] -> z
         v -> fail ("Non Bool in ifV: "++show v++"\n")
     }

------------------------------------------------------------------
-- A pattern can be matched against a value strictly, in which case the value
-- is forced enough to find a value for every variable in the pattern.
-- Or, it can build a computation that forces the value when the computation
-- is pulled on.

matchStrict prefix p v env = mPatStrict prefix [] (expandPat env p) v

mPatStrict :: Prefix -> EnvFrag -> Pat -> V -> FIO (Maybe EnvFrag)
mPatStrict prefix es (Pann p typ) v = mPatStrict prefix es p v
mPatStrict prefix es (Pvar s) v = return(Just((s,v):es))
mPatStrict prefix es (Paspat n p) v = mPatStrict prefix ((n,v):es) p v
mPatStrict prefix es  Pwild v = return(Just es)
   -- Only analyze v if we have to, otherwise mPatStrict is too strict
mPatStrict prefix es p v = analyzeWith (mf p) v
  where mf (Plit x) (Vlit y) = if x==y then return(Just es) else return Nothing
        mf (Pprod x y) (Vprod u v) =
           m2PatStrict prefix es x y u v
        mf (Psum i x) (Vsum j y) =
           if i==j then mPatStrict prefix es x y else return Nothing
        mf (Pexists p) v = mPatStrict prefix es p v
        {-  -- ** Begin Special Case for Strings **
        mf (Pcon (Global ":") [p,ps]) (VChrSeq (v:vs)) =
            m2PatStrict prefix es p ps (Vlit (Char v)) (VChrSeq vs)
        mf (Pcon (Global "[]") []) (VChrSeq "") = return(Just es)
        mf (Pcon (Global "[]") []) (VChrSeq _) = return Nothing
        -- ** End Special Case for Strings ** -}

        mf (Pcon n ps) (Vcon (c,_) vs) =
           if n==c then mStrictPats prefix ps vs es else return Nothing
        mf p v = return Nothing
        --mf p v = fail ("At end of matchStrict: "++ show p++
        --               " does not match "++show v)

m2PatStrict prefix es p ps v vs =
 do { z <- mPatStrict prefix es p v
    ; case z of
        Just es2 -> mPatStrict prefix es2 ps vs
        Nothing -> return Nothing}


mStrictPats prefix [] [] es = return(Just es)
mStrictPats prefix (p:ps) (v:vs) es =
   do { z <- mPatStrict prefix es p v
      ; case z of
          Just es2 -> mStrictPats prefix ps vs es2
          Nothing -> return Nothing}
mStrictPats prefix _ _ es = return Nothing


-- matchPatLazy is a total function. It never fails when it is called.
-- It performs lazy pattern matching. It does this by
-- building a value which is lazy and an environment fragment. When this
-- lazy value is pulled upon it incrementally matches itself against the
-- pattern passed to matchPatLazy. If the matching fails, the failure becomes
-- evident when the value is pulled upon, not when matchPatLazy is called.
-- The env frag also binds the pattern variables to similar lazy values.
-- Note that the second arg to matchPatLazy MUST BE A (Vlazy ref).
-- The function is monadic ONLY because we need to allocate new IORefs
-- to build the lazy values, and to generate new symbols for the env frag.
-- This function is used to implement recursive value declarations i.e.
-- pat = exp. We need to eval exp in an environment with bindings for the
-- variables in pat, but we need the value of exp to get those bindings.

matchPatLazy :: Pat -> V -> FIO (V,EnvFrag)
matchPatLazy (Pann p typ) v = matchPatLazy p v
matchPatLazy (Pexists p) v = matchPatLazy p v
matchPatLazy (Pvar s) v = return(v,[(s,v)])
matchPatLazy (Paspat s p) v = do { (v2,xs) <- matchPatLazy p v; return(v2,(s,v):xs)}
matchPatLazy Pwild v = return(v,[])
matchPatLazy (Plit x) (val@(Vlazy _ _)) =
   do { let id (v@(Vlit y))
               | x==y = return v
               | True = fail ("Bad literal: "++show x++" /= "++show y)
            id v = fail ("Not a literal: "++show v)
      ; v <- vlazy (analyzeWith id val)
      ; return(v,[])}
matchPatLazy (Pprod p1 p2) (val@(Vlazy _ _)) =
   do { let fst (Vprod x y) = return x
            fst v = fail ("\nMatching fails. Not a pair: "++show v)
            snd (Vprod x y) = return y
            snd v = fail ("\nMatching fails. Not a pair: "++show v)
      ; v1 <- vlazy (analyzeWith fst val)
      ; v2 <- vlazy (analyzeWith snd val)
      ; (u1,xs) <- matchPatLazy p1 v1
      ; (u2,ys) <- matchPatLazy p2 v2
      ; let v = Vprod u1 u2
      ; return(v,xs++ys)}
matchPatLazy (pat@(Psum i p)) (val@(Vlazy _ _)) =
   do { let select (v @ (Vsum j y))
               | i==j = return y
               | True = fail ("\nMatching fails. "++show pat++
                              " does not match "++show v)
            select v = fail ("Matching fails. Not a sum: "++show v)
      ; v1 <- vlazy (analyzeWith select val)
      ; (u1,xs) <- matchPatLazy p v1
      ; return(Vsum i u1,xs)
      }
matchPatLazy (Pcon c ps) (val@(Vlazy _ _)) =
   do { let get i (v @ (Vcon (m,exts) vs))
                 | c==m = return(vs !! i)
                 | True = fail ("\nMismatch on lazy pattern match of constructor, "++show c++" does not match "++show v)
            acc (p,v) (us,xs) = do { (u,x) <- matchPatLazy p v; return(u:us,x++xs)}
      ; vs <- mapM (\ i -> vlazy (analyzeWith (get i) val))
                   [0 .. length ps - 1]
      ; (us,xs) <- foldrM acc ([],[]) (zip ps vs)
      ; return(Vcon (c,Ox) us,xs)  ---EXT
      }
matchPatLazy p v = fail ("Non lazy value passed to matchPatLazy\n"++show p++"\n"++show v)



-------------------------------------------------------------------
-- dealing with First class patterns

evalPat2 ns p = makeV ns []
  where makeV (n:ns) pairs = Vprimfun "pairs" (\ v -> return(makeV ns ((n,v):pairs)))
        makeV [] pairs = pat2val pairs p

pat2val env (Pann p t) = pat2val env p
pat2val env (Plit l) = Vlit l
pat2val env (Pprod x y) = Vprod (pat2val env x) (pat2val env y)
pat2val env (Psum inj y) = Vsum inj (pat2val env y)
pat2val env (Pcon nm ps) = Vcon (nm,Ox) (map (pat2val env) ps) ---EXT
pat2val env (Pvar s) =
   case lookup s env of
     Nothing -> error ("Unknown var in pat evaluation: "++show s)
     Just v -> v
pat2val env p =
  error ("Illegal pattern in rhs of pattern declaration: "++(show p))

mapPat :: (Pat -> Pat) -> Pat -> Pat
mapPat env (Plit c) = Plit c
mapPat env (Pvar c) = Pvar c
mapPat env (Pprod x y) = Pprod (env x) (env y)
mapPat env (Psum x y) = Psum x (env y)
mapPat env (Pexists y) = Pexists (env y)
mapPat env (Paspat x p) = Paspat x (env p)
mapPat env Pwild = Pwild
mapPat env (Pcon n ps) = Pcon n (map env ps)
mapPat env (Pann p t) = Pann (env p) t
mapPat env (ExtP ep) = ExtP(fmap env ep)

expandPat :: Env -> Pat -> Pat
expandPat env (Pcon n ps) =
  let ps2 = (map (expandPat env) ps)
  in case static n env of
      Nothing -> Pcon n ps2
      Just(Vpat _ f g) -> f ps2
      Just v -> Pcon n ps2
expandPat env x = mapPat (expandPat env) x


funcPat :: [Var] -> Pat -> ([Pat]->Pat)
funcPat ns p ps = build ns p
  where build ns (Pvar x) =
           case pos x ns of
              Nothing -> error ("Unknown pat variable in expansion: "++show x)
              Just m -> ps !! m
        build ns p = mapPat (build ns) p


----------------------------------------------------------------------------
-- elab "evaluates" a Dec in an environment, getting a new environment. Which
-- contain the bindings for the names defined in the Dec. Because Dec's come
-- in mutually recursive sets, we need to handle this appropriately. By the
-- use of the fixpoint on the monad, "magic" and the env returned are
-- identical.

elab :: Prefix -> Env -> Env -> Dec -> FIO Env
elab prefix magic init (Pat loc nm args body) =
  return(extendV [(nm,(Vpat nm (funcPat args body) (evalPat2 args body)))] init)
elab prefix magic init (d@(Val loc p b ds)) =
  do { v <- vlazy(do { env2 <-  elaborate Tick ds magic
                     ; evalBody env2 b (fail "Body in Decl has no True case")})
     ; (u,frag2) <- matchPatLazy p v
     ; return(extendV frag2 init)}
elab prefix magic init (Fun loc nm _ cs) =
     -- tranform    f x y = e1    to    f m n = case (n,m) of
     --             f a b = e2                   (x,y) -> e1
     --                                          (a,b) -> e2
  do { let new (Pvar (Global s)) = do { n <- fresh; return(Alpha s n)}
           new _ = do { n <- fresh; return(Alpha "p" n)}
           getpat (loc,pat,body,ds) = pat
     ; newNames <- mapM new (getpat (head cs))
     ; let tupleUpPats (loc,ps, b,ds) = (loc,patTuple ps,b,ds)
           tuple = expTuple(map Var newNames)
           patterns = (map Pvar newNames)
           caseExp = Case tuple (map tupleUpPats cs)
           u = makeLam patterns caseExp [] [] magic
           free = getFreeTermVars newNames caseExp
     ; return (extendV [(nm,u)] init) }
elab prefix magic init (Data loc b strata nm sig args constrs derivs exts) =
    return(extendV xs init)
 where xs = map f constrs
       f (Constr loc exs cname args eqs) = (cname,(mkFun (show cname) (Vcon (cname,exts)) (length args) []))
elab prefix magic init (GADT l p t k cs ds exts) =
   -- warnM [Ds "\nelab ",Ds (show t),Ds " ",Ds (show exts)] >>
   return(extendV xs init)
 where xs = map f cs
       f (loc,cname,allv,preds,ty) =
            (cname,(mkFun (show cname) (Vcon (cname,exts)) (size ty) []))
       size (Rarrow' x y) = 1 + size y
       size (Karrow' x y) = 1 + size y
       size _ = 0

elab prefix magic init (TypeSig loc nm t) = return init
elab prefix magic init (Prim loc nm t) =
   case lookup nm primitives of
     Just v -> return(extendV [(nm,v)] init)
     Nothing -> fail ("Can't find implementation for primitive: "++show nm)
elab prefix magic init (Flag _ _) = return init
elab prefix magic init (Reject s ds) =
   handle 4 (do { outputString ("Elaborating Reject"++show ds)
                ; env2 <-  elaborate Tick ds magic
                ; fail ("Reject test: "++s++" did not fail.")})
            (\ s -> return init)
elab prefix magic init (AddTheorem loc xs) = return init
elab prefix magic init (TypeSyn loc nm args t) = return init
elab prefix magic init (TypeFun loc nm k ms) = return init
elab prefix magic init d = fail ("Unknown type of declaration:\n"++(show d))


elaborate prefix ds env0 =
    do { env1 <- fixFIO h
       ; fixup ((foldr count 0 ds)) env1 }
  where h magic = foldM (elab prefix magic) env0 ds


count d n = let x = boundBy d in length (binds x) + n

-- For each of the "n" things defined by the mutually recursive [Dec],
-- force the thunk that was originally set up then rebind the name to
-- the resulting value in the new environment.

fixup 0 env = return env
fixup n (Ev ((nm,v):vs) m) =
   do { --outputString ("Fixing: "++show nm);
        u <- analyzeWith return v
      ; (Ev us _) <- fixup (n-1) (Ev vs m)
      ; return(Ev ((nm,u):us) m) }


-- The initial runtime environment
env0 = extendV (map f vals) empty
  where f (name,(value,typ)) = (Global name,value)


make x  = (to x,  gen(typeOf x))
make1 x = (to1 x, gen(typeOf x))
make2 x = (to2 x, gen(typeOf x))
make3 x = (to3 x, gen(typeOf x))

makeCon1 (name@(nm,ext)) x = (mkFun (show nm) (Vcon (name)) 1 [], gen(typeOf x))
makeCon2 (name@(nm,ext)) x = (mkFun (show nm) (Vcon (name)) 2 [], gen(typeOf x))


mkFun :: String -> ([V] -> V) -> Int -> [V] -> V
mkFun s f 0 vs = f (reverse vs)
mkFun s f n vs = Vprimfun s (\ v -> return(mkFun s f (n-1) (v:vs)) )



vals :: [(String,(V,Sigma))]
vals =
 [("+",make2 ((+)::Int -> Int -> Int))
 ,("*",make2 ((*)::Int -> Int -> Int))
 ,("-",make2 ((-)::Int -> Int -> Int))
 ,("div",make2 ((div)::Int -> Int -> Int))
 ,("rem",make2 ((rem)::Int -> Int -> Int))
 ,("mod",make2 ((mod)::Int -> Int -> Int))
 ,("negate",make1((\ x -> 0-x)::Int -> Int))
 ,("<", make2 ((<) ::Int -> Int -> Bool))
 ,("<=",make2 ((<=)::Int -> Int -> Bool))
 ,(">", make2 ((>) ::Int -> Int -> Bool))
 ,(">=",make2 ((>=)::Int -> Int -> Bool))
 ,("==",make2 ((==)::Int -> Int -> Bool))
 ,("/=",make2 ((/=)::Int -> Int -> Bool))

 ,("#+",make2 ((+)::Float -> Float -> Float))
 ,("#*",make2 ((*)::Float -> Float -> Float))
 ,("#-",make2 ((-)::Float -> Float -> Float))
 ,("#/",make2 ((/)::Float -> Float -> Float))
 ,("negateFloat",make1((\ x -> 0-x)::Float -> Float))
 ,("#<", make2 ((<) ::Float -> Float -> Bool))
 ,("#<=",make2 ((<=)::Float -> Float -> Bool))
 ,("#>", make2 ((>) ::Float -> Float -> Bool))
 ,("#>=",make2 ((>=)::Float -> Float -> Bool))
 ,("#==",make2 ((==)::Float -> Float -> Bool))
 ,("#/=",make2 ((/=)::Float -> Float -> Bool))
 ,("intToFloat",make1(fromIntegral ::Int -> Float))
 ,("round",make1(round :: Float -> Int))
 ,("truncate",make1(truncate :: Float -> Int))

 ,("eqStr", make2 ((==)::String -> String -> Bool))
 ,("chr",make1 chr)
 ,("ord",make1 ord)

 ,("putStr",make1 (putStr :: String -> IO ()))
 ,("getStr",make(getLine::IO String))

 ,("&&",make2 (&&))
 ,("||",make2 (||))
 ,("not",make1 not)

 ,("True",make True)
 ,("False",make False)

 ,(":",makeCon2 (Global ":",Lx("","[]",":")) ((:):: A -> [A] -> [A]))
 ,("null",make1 (null:: [A] -> Bool))
 ,("[]",make([]::[A]))
 ,("++",make2((++):: [A] -> [A] -> [A]))
 ,("(,)",make2((,):: A -> B -> (A,B)))

 ,("undefined", (Vbottom,gen(typeOf(undefined :: A))))

 ,("Nothing",make(Nothing::(Maybe A)))
 ,("Just",makeCon1 (Global "Just",Ox) (Just::(A -> Maybe A)))

 ,("show",make1(show :: A -> String))
 ,("unsafeCast",make1(unsafeCast:: A -> B))

 ,("mimic",(mimic,gen(typeOf(undefined :: (A -> B) -> A -> B))))
 ,("strict",(strict,gen(typeOf(undefined :: (A -> A)))))

-- ,(".",make2(($)::(A -> B) -> A -> B))


 ,("trace",(traceV,gen(typeOf(undefined :: String -> A -> A))))
 ,("error",(to errorC,gen(typeOf(undefined :: String -> A))))
 ,("fresh",(freshV,gen(typeOf(undefined :: Char -> Symbol))))
 ,("swap",(swapV,gen(typeOf(undefined :: Symbol -> Symbol -> A -> A))))
 ,("symbolEq",(symbolEqV,gen(typeOf(undefined :: Symbol -> Symbol -> Bool))))
 ,("labelEq",(labelEqV,gen(typeOf(undefined :: Label T1 -> Label T2 -> Maybe(Equal T1 T2)))))
 ,("freshLabel",(freshLabelV,gen(typeOf(undefined:: IO HiddenLabel))))
 ,("newLabel",(newLabelV,gen(typeOf(undefined:: String -> HiddenLabel))))

 ,("freshen",(freshenV,gen(typeOf(undefined :: A -> (A,[(Symbol,Symbol)])))))
 ,("run",(to run,runType))
 ,("lift",(reifyV,liftType))

 ,("returnIO",(returnIO,gen(typeOf(undefined :: A -> IO A))))
 ,("bindIO",(bindIO,gen(typeOf(undefined :: IO A -> (A -> IO B) -> IO B))))
 ,("failIO",(failIO,gen(typeOf(undefined :: String -> IO A))))
 ,("handleIO",(handleIO,gen(typeOf(undefined :: IO A -> (String -> IO A) -> IO A))))

 --,("Eq",(Vcon (Global "Eq") [],sigma4Eq))
 --,("Hide",(Vprimfun "Hide" (\ v -> return(Vcon (Global "Hide") [v])),sigma4Hide))

 {-
 ,("newPtr",(newPtr,gen(typeOf(undefined :: IO (Hidden Ptr)))))
 ,("readPtr",(readPtr,gen(typeOf(undefined :: Ptr A -> IO (Maybe A)))))
 ,("writePtr",(writePtr,gen(typeOf(undefined :: Ptr A -> A -> IO () ))))
 ,("nullPtr",(nullPtr,gen(typeOf(undefined :: Ptr A -> IO Bool ))))
 ,("initPtr",(initPtr,gen(typeOf(undefined :: Ptr A -> B -> IO(Eql A B)))))
 ,("samePtr",(samePtr,gen(typeOf(undefined :: Ptr A -> Ptr B -> IO(Eql A B)))))
 -}

 ,("$",(dollar,gen(typeOf(undefined :: (A -> B) -> A -> B))))
 ,(".",(composeV,gen(typeOf(undefined :: (A -> B) -> (C -> A) -> (C -> B)))))
 ]



----------------------------------------------------------------------
-- List operators that know about dual representations for Strings
-- I'm still not sure that these are a good idea. Especially since
-- the interaction with Vlazy seems over specified
-- This code is temporarily not used.

listVals =
  [(":",(consV,gen(typeOf(undefined :: A -> [A] -> [A]))))
  ,("null",(nullV,gen(typeOf(undefined:: [A] -> Bool))))
  ,("++",(appendV,gen(typeOf(undefined::[A] -> [A] -> [A]))))
  ]

nullV = lift1 "null" g
  where g (VChrSeq "") = return trueExp
        g (VChrSeq _) = return falseExp
        g (Vcon (Global "[]",_) []) = return trueExp
        g (Vcon (Global ":",_) [x,y]) = return falseExp
        g v = fail ("Bad arg to null: "++show v)

-- cons has to be lazy since it is a constructor function so it
-- can't use analyzeWith, but it also has to handle strings specially

consV = Vprimfun ":" g
  where g (Vlit (Char c)) = return(Vprimfun ("(:) "++show c) (charCons c))
        g v               = return(Vprimfun ("(:) "++show v) (f v))
        f v vs = return(Vcon (Global ":",Lx("","[]",":")) [v,vs])

charCons :: Char -> V -> FIO V
charCons c (VChrSeq cs) = return(VChrSeq (c:cs))
charCons c (Vcon (Global "[]",_) []) = return(VChrSeq [c])
charCons c (v@(Vcon (Global ":",_) [_,_])) =
     do { cs <- list2seq v; return(VChrSeq (c:cs))}
charCons c vs = return(Vcon (Global ":",Lx("","[]",":")) [Vlit (Char c),vs])

list2seq :: V -> FIO String
list2seq v = analyzeWith f v
  where f (VChrSeq cs) = return cs
        f (Vcon (Global "[]",_) []) = return ""
        f (Vcon (Global ":",_) [c,cs]) =
          do { Vlit(Char x) <- analyzeWith return c
             ; xs <- list2seq cs
             ; return(x:xs)}

appendV = lift2 "++" g
  where g (VChrSeq xs) (VChrSeq cs) = return(VChrSeq (xs ++ cs))
        g (VChrSeq xs) (Vcon (Global "[]",_) []) = return(VChrSeq xs)
        g (VChrSeq xs) (v@(Vcon (Global ":",_) [_,_])) =
              do { cs <- list2seq v; return(VChrSeq (xs ++ cs))}
        g (Vcon (Global ":",_) [x,xs]) ys = analyzeWith h xs
           where h zs = case x of
                         Vlit (Char c) -> do { cs <- g zs ys; charCons c cs}
                         x -> cons x (g zs ys)
        g (Vcon (Global "[]",_) []) ys = return ys
        g x y = fail ("Bad args to (++) "++show x++" and "++show y)
        cons x xs = do { ys <- xs; return(Vcon (Global ":",Lx("","[]",":")) [x,ys])}

----------------------------------------------------------------------

run = lift1 "run" g where
  g (Vcode a xs) = eval xs a
  g v = fail ("Non code object in run: "++show v)


reifyV = lift1 "lift" f where
  f x = do { v <- reify x; return(Vcode v empty)}

reify :: Monad m => V -> m Exp
reify (Vlit x) = return(Lit x)
reify (Vsum j v) = do { x <- reify v; return(Sum j x)}
reify (Vprod x y) = do { a <- reify x; b <- reify y; return(Prod a b)}
reify (Vcon (c,_) vs) = do { us <- mapM reify vs; return(f (Var c) us)}
  where f g [] = g
        f g (x:xs) = f (App g x) xs
reify v = return(Lit(CrossStage v))
-- reify v = fail ("\nRun-time error ******\nCannot reify: "++show v)

freshV = lift1 "fresh" f
  where f (Vlit (Char c)) = do { nm <- fresh; return(mkSymbol nm) }
        f v = fail ("\nRun-time error ******\nNon char as argument to fresh: "++show v)

swapV = lift2 "swap" h
  where h (Vlit (Symbol s1)) (Vlit (Symbol s2)) = return(Vprimfun (nam2 "swap" s1 s2) (downSwap [(s1,s2)] return))
        h (Vlit (Symbol _)) v = fail ("Non Name as argument to swap: "++show v)
        h v (Vlit (Symbol _)) = fail ("Non Name as argument to swap: "++show v)

errorC = lift1 "error" g where
  g v = fail(from v)


mimic = Vprimfun "mimic" mim  -- Don't use lift2 or analyzeWith here !!
  where mim (Vpat nm g f)  = mim f
        mim f = return(Vprimfun (nam1 "mimic" f) h)
           where h (val@(Vlazy _ _)) = vlazy (analyzeWith (applyV (show f) f) val)
                 h (Vswap cs u) = do {v <- h u; return(Vswap cs v)}
                 h v = applyV (show f++" inside call to mimic") f v

strict = lift1 "strict" return

traceV = lift1 "trace" f
  where f s = outputString mess >> return (Vprimfun (nam1 "trace" mess) h)
            where mess = from s
                  h v = return v


-- Primitive functions encode a string that can be printed.
-- When we construct a multi-argument primitive we build nested
-- Vprimfun values. The string that names the primitive "adds" extra
-- arguments as the primitive is applied to further arguments.
-- name1 and name2 help build these strings

nam1 string value = "(" ++ string ++ " " ++ show value ++ ")"
nam2 string v1 v2 = "(" ++ string ++ " " ++ show v1 ++ " " ++ show v2 ++ ")"

applyV message f v = analyzeWith apply f
  where apply (Vprimfun s h) =  h v
        apply (Vf f push swap) = f v
        apply (Vpat nm g h) = applyV message h v
        apply v = fail ("Bad thing applied as function: "++show v++"\nin "++ message)


-- (f $ y) = f y
dollar = Vprimfun "($)" f
  where f v1 = return(Vprimfun (nam1 "$" v1) h)
               where h v2 = applyV (nam2 "$" v1 v2) v1 v2


-- (f . g) = \ v -> f (g v)
composeV = Vprimfun "(.)" f
  where f v1 = return(Vprimfun (nam1 "." v1) h)
          where h v2 = return(Vprimfun (nam2 "." v1 v2) g)
                  where g x = do { g2 <- applyV "(.)" v2 x
                                 ; applyV "(.)" v1 g2 }




-----------------------------------------------------------------
-- IO primitives

returnIO :: V
returnIO = Vprimfun "returnIO" f
  where f v = return(Vfio [] (return (Right v)))

bindIO :: V
bindIO = Vprimfun "bindIO" (analyzeWith f) where
  f action@(Vfio cs c1) = return(Vprimfun name g) where
     name = ("bindIO "++show action)
     g fun =  return(Vfio [] c2) where
        c2 = do { choice <- c1;
                ; case choice of
                    Right a -> do { let fresh_a = swaps cs a
                                        message = (show fun++" "++show fresh_a)
                                  ; ans <- applyV message fun fresh_a
                                  ; case ans of
                                     Vfio cs2 action -> swaps cs2 action
                                     v -> fail ("Second argument to bindIO does not return an IO action: "++ show v)}
                    Left s -> return(Left s) }
  f v = fail("Non IO action as first arg to bindIO: "++show v)

instance Swap a => Swap (FIO a) where
  swaps [] x = x
  swaps cs comp = (do { x <- comp; return(swaps cs x)})

failIO :: V
failIO = Vprimfun "failIO" f
  where f arg = do { string <- stringV arg
                   ; return(Vfio [] (return (Left string))) }
          where stringV :: V -> FIO String
                stringV v = analyzeWith help v where
                   help (Vcon (Global "[]",Lx("","[]",":")) []) = return []
                   help (Vcon (Global ":",Lx("","[]",":")) [Vlit (Char x),y]) =
                    do {xs <- stringV y; return(x:xs) }
                   help _ = fail ("Non String as arg to failIO: "++show arg)

handleIO :: V
handleIO = Vprimfun "handleIO" (analyzeWith f) where
  f action@(Vfio cs c1) = return(Vprimfun name (analyzeWith g)) where
     name = ("handleIO "++show action)
     g fun =  return(Vfio [] c2) where
        c2 = do { choice <- c1;
                ; case choice of
                    Right a -> return(Right a)
                    Left s -> do { let arg = to s
                                       message = show fun ++" "++show arg
                                 ; a <- applyV message fun arg
                                 ; case a of
                                    Vfio cs action -> (do { u <- action; return(swaps cs u) })
                                 }}

----------------------------------------------------------
-- Atom Primitives

fresh2 = Vfio [] (do { nm <- fresh; return(Right(mkSymbol nm)) })

sameAtom = lift2 "sameAtom" f  where
  f (Vlit (Symbol s1)) (Vlit (Symbol s2)) =
                  if s1 == s2 then return(Vcon (Global "Just",Ox) [Vcon (Global "Eq",Ox) []])
                              else return(Vcon (Global "Nothing",Ox) [])
  f (Vlit (Symbol s1)) v = fail ("Non Name as argument to sameAtom: "++show v)
  f v (Vlit (Symbol s1)) = fail ("Non Name as argument to sameAtom: "++show v)



freshU (Vlit (Symbol s)) = (do { nm <- fresh; return(Vlit(Symbol nm),[(s,nm)])})
freshU (v@(Vlit x)) = return(v,[])
freshU (Vsum inj v) = do {(u,cs) <- freshU v; return(Vsum inj u,cs)}
freshU (Vprod a b) = do {(u,cs)<-freshU a; (v,ds)<-freshU b; return(Vprod u v,cs++ds)}
freshU (Vcon x vs) = do { (us,cs) <- f vs; return(Vcon x us,cs)}
  where f [] = return([],[])
        f (x:xs) = do { (a,cs) <- freshU x; (bs,ds)<-f xs; return(a:bs,cs++ds)}
freshU (Vpat x f v) = do {(u,cs) <- freshU v; return(Vpat x f u,cs)}
freshU (Vswap cs v) = freshU (swaps cs v)
freshU v = fail ("Can't freshen this value: "++show v)


freshenV = Vprimfun "freshen" (analyzeWith f) where
  f v = do { (u,cs) <- freshU v; return(Vprod u (to (map g cs)))}
  g (x,y) = (mkSymbol x,mkSymbol y)

symbolEqV = Vprimfun "symbolEq" (analyzeWith f) where
  f (Vlit (Symbol s1)) = return(Vprimfun (nam1 "symbolEq" s1) (analyzeWith (g s1)))
  g s1 (Vlit (Symbol s2)) = return(to (s1 == s2))

labelEqV = Vprimfun "labelEq" (analyzeWith f) where
  f (Vlit (Tag s1)) = return(Vprimfun (nam1 "labelEq" s1) (analyzeWith (g s1)))
  g s1 (Vlit (Tag s2)) = if s1==s2
                            then return(Vcon (Global "Just",Ox) [Vcon (Global "Eq",Ox) []])
                            else return(Vcon (Global "Nothing",Ox) [])

freshLabelV = Vfio [] f where
  f = do { n <- nextInteger ; return(Right(Vcon (Global "Hidden",Ox) [Vlit (Tag ("#"++short n))]))}

newLabelV =  Vprimfun "newLabel" (analyzeWith f) where
  f str = return(Vcon (Global "Hidden",Ox) [Vlit (Tag (from str))])

fuse = lift2 "fuse" f where
  f a b = return(Vprod a b)

melt = Vprimfun "melt" (analyzeWith f) where
  f (Vprod a b) = return(Vfio [] comp)
     where comp = do { (u,cs) <- freshU a; return(Right(Vprod u (swaps cs b))) }
  f x = fail ("Arg to melt is not a fusion: "++show x)

-----------------------------------------------------------
-- interface to the "primitive" decl

primitives :: [(Var,V)]
primitives = map f xs where
  f (x,y) = (Global x,y)
  xs = [("returnIO",returnIO),("bindIO",bindIO),("failIO",failIO),("handleIO",handleIO)
       ,("newPtr",newPtr),("readPtr",readPtr),("writePtr",writePtr)
       ,("nullPtr",nullPtr),("initPtr",initPtr),("samePtr",samePtr)
       ,("freshAtom",fresh2),("same",sameAtom),("swapAtom",swapV)
       ,("fuse",fuse),("melt",melt)
       ] ++ parserPairs



