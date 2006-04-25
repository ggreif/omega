-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Tue Apr 25 12:54:27 Pacific Daylight Time 2006
-- Omega Interpreter: version 1.2.1

module Commands (commands,dispatchColon,execExp,drawPatExp
                ,letDec,commandF,notDup,foldF) where

import Infer2
import RankN(pprint)
import Syntax
import Monads(FIO(..),unFIO,runFIO,fixFIO,fio,resetNext
             ,write,writeln,readln,unTc,tryAndReport,fio)
import Version(version,buildtime)
import List(find)
import LangEval(Env(..),env0,eval,elaborate,Prefix(..),mPatStrict,extendV)
import Char(isAlpha,isDigit)
import ParserDef(getInt)
import Auxillary(plist,plistf)
import Monads(report)

--------------------------------------------------------
-- Build a table of    :com str    commands

-- :q
qCom tenv _ = error "quitting"

-- :t (4 + 2)
tCom tenv x =
   case getVar (Global x) tenv of
     Just(sigma,lev,exp) ->
       do { writeln (x++" :: "++(pprint sigma)) -- ++"\n"++sht t)
          ; return (tenv) }
     Nothing -> do { writeln ("Unknown name: "++x); return(tenv)}

-- :env map
envCom tenv s = envArg tenv s

-- :r
rCom elab sources tenv s =
  do { n <- readInt (length sources) s
     ; new <- elabManyFiles elab (take n sources) (initTcEnv{verbose = verbose tenv})
     ; return new }

-- :v
vCom tenv s =
  do { writeln version
     ; writeln buildtime
     ; return tenv}

-- :k Int
kCom tenv x =
 case (getkind x tenv) of
   Nothing ->
     do { (rho,t) <- parseAndKind tenv x
        ; writeln (x++" :: "++(pprint rho)++"  = " ++ pprint t)
        ; return (tenv)}
   Just(k,t,tree) ->
     do { writeln (x++" :: "++(pprint k)++"\n" ++ tree)
        ; return (tenv)}

-- :l file.prg
lCom elabFile tenv file =
   do { writeln ("Loading file "++file)
      ; elabFile file (tenv) }

-- :set verbose
setCom tenv mode = setCommand mode True tenv

-- :clear verbose
clearCom tenv mode = setCommand mode False tenv

-- :e
eCom tenv s =
  do { writeln "Back to inital state"
     ; return initTcEnv }

-- :rules LE
rulesCom tenv s =
  let rs = getRules s tenv
      f newstyle = writeln(pprint newstyle);
  in do { writeln "rules"
        ; mapM f rs
        ; return tenv}

-- :?
questionCom tenv s  = writeln commands >> return tenv

-- :pre
preCom tenv s = writeln predefined >> return tenv

-- :n {plus n Z}
nCom tenv x = tcInFIO tenv(narrowString tenv 5 x)

-------------------------------------------------------------
-- Command interfaces for each of the kinds of interactive input

-- (ColonCom com str)
-- top level function, dispatches on the 'com' in ':com'

dispatchColon table tenv com str =
    case find (p com) table of
       Just (x,f,info) -> f tenv str
       Nothing -> fail ("Unknown command :"++str)
  where p com (x,f,info) = x==com

commandF s f =
  [("q",    qCom,    ":q           quit\n")
  ,("t",    tCom,    ":t           display type of expression\n")
  ,("env",  envCom,  ":env n       display info for first 'n' items\n" ++
                     ":env str     display info for items with 'str' in their names\n")
  ,("r",    rCom f s,":r file      reload file into system\n")
  ,("v",    vCom,    ":v           display version info\n")
  ,("k",    kCom,    ":k type      display kind of type expression\n")
  ,("l",    lCom f,  ":l file      load file into system\n")
  ,("set",  setCom,  ":set         list all the Mode variables and their settings\n" ++
                     ":set mode    set the Mode variables X (where 'mode' is a prefix of X) to True\n")
  ,("clear",clearCom,":clear mode  clear the Mode variables X (where 'mode' is a prefix of X) to False\n")
  ,("e"    ,eCom,    ":e           reset system to initial configuration (flush definitions)\n")
  ,("rules",rulesCom,":rules name  display rules for 'name'\n")
  ,("pre",  preCom,  ":pre         display declarations for all predefined types\n")
  ,("n",    nCom,    ":n type      narrow type expression\n")
  ,("?",questionCom, ":?           display list of legal commands (this message)\n")
  ]

commands = concat ([
  "let v = e    bind 'v' to 'e' in interactive loop\n",
  "v <- e       evaluate IO expression 'e' and bind to 'v'\n",
  "exp          read-typecheck-eval-print 'exp'\n"
  ] ++ map (\ (c,f,mess) -> mess) (commandF [] undefined))


-- (ExecCom e)
-- 5 + 2
execExp tenv e =
   do { (t,e') <- wellTyped tenv e
      ; v <- (eval (runtime_env tenv) e')
      ; u <- runAction v
      ; writeln ((show u)++ " : "++(pprint t))
      ; return (tenv) }

-- (DrawCom p e)
-- (m,n) <- exp
drawPatExp tenv p e =
 do { (e',p',env',t) <- ioTyped tenv p e
    ; v <- (eval (runtime_env env') e')
    ; u <- runAction v
    ; z <- mPatStrict Tick [] p' u
    ; case z of
       Just frag -> let rtenv = extendV frag (runtime_env env')
                    in do { writeln ((show u)++ " : "++(pprint t))
                          ; return(env' { runtime_env = rtenv }) }
       Nothing -> do { writeln ("Pattern "++show p++" does not match "++show v)
                     ; return tenv }
    }

-- (LetCom d)
-- let x = 5
letDec elabDs tenv d =
  do { mapM (notDup tenv "Keyboard input") (fst (freeOfDec d))
     ; ans <- foldF elabDs (tenv) [[d]]
     ; writeln ""
     ; return ans
     }

---------------------------------------------------------
-- Helper functions for commands

envArg tenv (s@(c:cs))
  | isDigit c = do { count <- (readInt 100 s)
                   ; showAllVals count tenv
                   ; return tenv }
  | isAlpha c = do { let subString [] ys = True
                         subString _ [] = False
                         subString (x:xs) (y:ys) =
                            if x==y then subString xs ys else subString s ys
                         p (Global nm,_) = subString s nm
                   ; showSomeVals p tenv
                   ; return tenv}
  | True = do { writeln ("Bad arg ':env "++s++"'"); return tenv}
envArg tenv [] = return tenv


-- Read an Int from stdin, and return nullNum on failure.
readInt nullNum s =
  if null s then return nullNum else getInt fail s

setCommand "" value tenv = do { writeln (plistf f "" modes "\n" "\n"); return tenv }
  where f (mode,bool) = mode++" = "++show bool
        modes = verbose tenv
setCommand mode value tenv = setMode mode value tenv

-- A toplevel expression of type IO can be executed

runAction v =
  case v of
    Vfio _ action ->
      do { writeln "Executing IO action"
         ; u <- action
         ; case u of
             Right v -> return v
             Left s -> fail ("Uncaught IO Error: "++s) }
    v -> return v

elabManyFiles elabFile [] env = return env
elabManyFiles elabFile (x:xs) env =
  do { env2 <- elabManyFiles elabFile xs env
     ; elabFile x env2}

foldF acc base [] = return base
foldF acc base (x:xs) = do { b <- acc x base
                           ; tryAndReport (foldF acc b xs)(report (return base)) }



-------------------------------------------------------------------------
-- Reports an error if "nm" already appears in the existing
-- type environment "tenv", "nm" comes from attempting load "file"

notDup tenv file nm =
  case getVarOrTypeName nm tenv of
    Nothing -> return ()
    Just s -> if (s `elem` ["Monad","Equal","Eq"])
              then return ()
              else (fail ("The name: "++ show s++" which is found in the"++
                    " environment is redefined in file "++file))

-- There are 2 name spaces. Value and Type.
-- We need to look up each name in the right environments
-- We also need to strip off the type cons prefix ( %name --> name )
-- which is added to names which are defined in Type Name space
-- before looking them up. A name is "flagged" if it starts with a '%'

getVarOrTypeName :: Var -> TcEnv -> Maybe String
getVarOrTypeName nm env
 | flagged nm = f (type_env env)
 | otherwise = case getVar nm env of
                Nothing -> Nothing
                Just(name,_,_) -> Just (varName nm)
 where orig = varName nm
       varName (Global ('%':s)) = s  -- strip off Type Con Prefix
       varName (Global s) = s
       varName (Alpha s n) = s
       -- varName (Alpha ('%':s) n) = s
       f [] = Nothing
       f ((y,t,k):xs) = if y== orig then return orig else f xs



