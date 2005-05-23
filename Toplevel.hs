-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Mon May 23 09:40:05 Pacific Daylight Time 2005
-- Omega Interpreter: version 1.1


module Toplevel where

import Version(version,buildtime)
import Time
import Syntax
import ParserDef(getInt,pCommand,parseString,Command(..)
                ,program,parseFile)
import LangEval(Env(..),env0,eval,elaborate,Prefix(..),mPatStrict,extendV)
import Monads(FIO(..),unFIO,runFIO,fixFIO,fio,resetNext
             ,write,writeln,readln,unTc,tryAndReport,fio)
import IO
import IOExts
import List(partition,(\\),nub)
import Auxillary(plist,plistf,foldrM,backspace,Loc(..),extendL,DispInfo)
import SCC(topSortR)
import Monad(when)
import Infer2
import RankN(pprint)
import System(getArgs)
import Data.FiniteMap
import Directory
import Char(isAlpha,isDigit)

-------------------------------------------------------------
-- The programmer interface: the top level loop.
-- it performs the read-eval-typecheck-print loop.
-- It catches exceptions, and ties all the other pieces together.



typeEnv0 = initTcEnv

-- Read an Int from stdin, and return nullNum on failure.

readInt nullNum s =
  if null s then return nullNum else getInt fail s
  
-- Perform one Read-Eval-Print action.

readEvalPrint :: [String] -> (TcEnv) -> FIO(TcEnv)
readEvalPrint sources tenv =
  do { input <- readln
     ; z <- parseString pCommand (backspace input [])
     ; case z of
        Left s -> do {writeln s; return (tenv) }

        Right(x,rest) ->
         case x of
          (ColonCom "q" _) -> error "quitting"
          (ColonCom "t" x) ->
             case getVar (Global x) tenv of
                Just(sigma,lev,exp) ->
                        do { writeln (x++" :: "++(pprint sigma)) -- ++"\n"++sht t)
                           ; return (tenv) }
                Nothing -> do { writeln ("Unknown name: "++x); return(tenv)}
          (ColonCom "env" s) -> envArg tenv s
          (ColonCom "r" s) ->
             do { n <- readInt (length sources) s
                ; new <- elabManyFiles (take n sources) (typeEnv0)
                ; return new
                }
          (ColonCom "v" _) -> do { writeln version
                                 ; writeln buildtime
                                 ; return tenv}
          (ColonCom "k" x) ->
             case (getkind x tenv) of
               Nothing -> do { (rho,t) <- parseAndKind tenv x
                             ; writeln (x++" :: "++(pprint rho)++"  = " ++ pprint t)
                             ; return (tenv)}
               Just(k,t) -> do { writeln (x++" :: "++(pprint k)++"  = " ++ pprint t)
                               ; return (tenv)}
          (ColonCom "l" file) ->
             do { writeln ("Loading file "++file)
                ; elabFile file (tenv) }
          (ColonCom "noisy" _) ->  return(mknoisy tenv)
          (ColonCom "silent" _) -> return(mksilent tenv)
          (ColonCom "e" _) ->
             do { writeln "Back to inital state"
                ; return (typeEnv0) }
          (ColonCom "rules" s) ->
             let rs = getRules s tenv
                 f x = writeln(pprint x);
             in do { writeln "rules"
                   ; mapM f rs
                   ; return tenv}
          (ColonCom x y) -> fail ("Unknown command :"++x)
          (ExecCom e) ->
             do { (t,e') <- wellTyped tenv e
                ; t1 <- fio getClockTime
                ; v <- (eval (runtime_env tenv) e')		
		; t2 <- fio getClockTime
		; u <- runAction v
                ; writeln ((show u)++ " : "++(pprint t))
		; t3 <- fio getClockTime
		; let evTime = diffClockTimes t2 t1
                      evPTime = diffClockTimes t3 t1
		--; writeln ( "\nTime1 = " ++ (show evTime))
		--; writeln ( "\nTime2 = " ++ (show evPTime))
                ; return (tenv) }
          (DrawCom p e) -> 
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
          (LetCom d) ->
             do { mapM (notDup tenv "Keyboard input") (fst (freeOfDec d))
                ; ans <- foldF elabDs (tenv) [[d]]
                ; writeln ""
                ; return ans
                }
          other -> do { writeln "Unknown command"; return(tenv) }
     }

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
       

-- Repeat Read-Eval-Print until the :q command is given

topLoop sources env = tryAndReport
  (do { write "prompt> "
      ; fio(hFlush stdout)
      ; env' <-  (readEvalPrint sources env)
      ; topLoop sources env'
      }) (report (topLoop sources env))

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

--topLoop :: (Env,TEnv IORef) -> FIO Env

--------------------------------------------------------
-- Error reporting funcions

-- Report an error then die.
errF :: DispInfo -> Loc -> Int -> String -> a
errF disp loc n s = error ("At "++show loc++"\n"++s)

-- Report an error, then continue with the continuation
report :: FIO a -> Loc -> DispInfo -> String -> FIO a
report continue Z   dis message = do { writeln message; continue }
report continue loc dis message =
   do { writeln ("\nNear "++(show loc)++"\n"++message); continue }

---------------------------------------------------------------------------
-- load just the prelude and then go into the toplevel loop

main :: IO ()
main = runFIO(do { writeln "loading the prelude (LangPrelude.prg)"
		 ; fio $ hSetBuffering stdout NoBuffering
		 ; fio $ hSetBuffering stdin  NoBuffering
		 ; env1 <- tryAndReport (elabFile "LangPrelude.prg" (typeEnv0))
		             (report (return (typeEnv0)))
                 ; topLoop ["LangPrelude.prg"] env1
                 ; return () }) errF


-- load the prelude and then load the file "s", and then go into the toplevel loop.

go :: String -> IO ()
go s =
  runFIO(do { writeln "loading the prelude (LangPrelude.prg)"
            ; env <- tryAndReport (elabFile "LangPrelude.prg" (typeEnv0))
		            (report (return (typeEnv0)))
            ; env2 <- elabFile s env
            ; topLoop [s,"LangPrelude.prg"] env2
            ; return () }) errF

-- Don't load the prelude, just load "s" then go into the toplevel loop.

run :: String -> IO ()
run  s = runFIO(do { writeln ("loading "++s)
		 ; env1 <- tryAndReport (elabFile s (typeEnv0))
		                        (report (return(typeEnv0)))
                 ; topLoop [s] env1
                 ; return () }) errF                 

-- Try to load a file, if it fails for any reason, exit the program
-- with an unrecoverable error. Used in testing, where failure means
-- a major error, something very bad (and unexpected), has happened

try_to_load s = 
   runFIO(do { writeln ("loading "++s)
             ; env1 <- tryAndReport (elabFile s (typeEnv0)) err2
             ; writeln (s++" successfully loaded")
             ; return () }) errF
  where err2 loc disp mess = error ("At "++show loc++"\n"++mess)
             
             
-- Get the file to "run" from the command line arguments, then "run" it

omega :: IO()
omega =
  do { args <- getArgs
     ; putStr (version++"\n")
     ; putStr ("Build Date: "++buildtime++"\n\n")
     ; case args of
        [] -> run "LangPrelude.prg"
        ("-tests" :_ ) -> alltests
        ("-prim" : kindf : typef : _) -> show_init_vals kindf typef
        (_ : _) -> let arg1 = head args
                   in if arg1=="-tests"
                         then alltests
                         else run arg1
     }

-------------------------------------------------------------------------------
-- elabDs is the interface to everything. Elaborates a mutually recursive [Dec]
-- other functions read the [Dec] from files and call this function

elabDs :: [Dec] -> TcEnv -> FIO TcEnv
elabDs ds (tenv) =
  do { let nam (Global s) = s
     ; write ((display (map nam (concat (map decname ds))))++" ")
     ; (tenv1,ds1,cs1) <- checkDecs tenv ds   -- type check the list
     --; mapM (writeln .show) ds
     --; mapM (writeln . show) ds1
     ; when (not (null cs1)) (fail ("2 Unsolved constraints: "++show cs1))
     ; env1 <- elaborate None ds1 (runtime_env tenv)  -- evaluate the list
     ; return(tenv1 { runtime_env = env1 })
     }

display [s] = s
display ss = plistf id "(" ss " " ")"


------------------------------------------------------------------
-- Get a [Dec] from a file name

parseDecs :: String -> FIO[Dec]
parseDecs file =
  do { x <- fio (parseFile program file)
     ; case x of
        Left s -> fail s
        Right(Program ds) -> return ds
     }

-------------------------------------------------------------------
-- Read a [Dec] from a file, then split it into imports and binding groups
-- uses elabDs to do the work.

elabFile :: String -> (TcEnv) -> FIO(TcEnv)
elabFile file (tenv) =
   do { all <- parseDecs file
      ; let (imports,ds) = partition importP all
            (dss,pairs) = topSortR freeOfDec ds 
      --; writeln (show(map freeOfDec ds))
      ; tenv2 <- importManyFiles imports tenv
      -- Check for multiple definitions in the file
      ; multDef ds (concat (map fst pairs))
      -- Check if any names are already declared
      ; mapM (notDup tenv file) (foldr (\ (exs,deps) ss -> exs++ss) [] pairs)
      ; tenv3 <- foldF elabDs (tenv2) dss
      ; writeln ("\n File "++file++" loaded.\n")
      ; return tenv3
      }

foldF acc base [] = return base
foldF acc base (x:xs) = do { b <- acc x base
                           ; tryAndReport (foldF acc b xs)(report (return base)) }

elabManyFiles [] env = return env
elabManyFiles (x:xs) env = do { env2 <- elabManyFiles xs env; elabFile x env2}

-------------------------------------------------------------------------
-- Omega has a very simple importing mechanism. A user writes:
-- import "xx.prg" (f,g,T)
-- to import the file named "xx.prg", all symbols with names "f", "g", "T"
-- (no matter what namespace they appear in) are imported into the
-- current environment. Usually "xx.prg" is a complete path as Omega's
-- notion of current directory is quite primitive.

importP (Import s vs) = True
importP _ = False

importManyFiles [] tenv = return tenv
importManyFiles (d:ds) tenv =
  do { next <- importFile d tenv; importManyFiles ds next }

importFile :: Dec -> TcEnv -> FIO TcEnv
importFile (Import name vs) tenv =
  case lookup name (imports tenv) of
     Just previous -> return tenv
     Nothing -> do { new <- elabFile name typeEnv0
                   ; return(importNames name vs new tenv) }

importNames :: String -> [Var] -> TcEnv -> TcEnv -> TcEnv
importNames name vs new old =
  old { imports = (name,new):(imports old)
      , var_env = addListToFM (var_env old) (filter p (fmToList (var_env new)))
      , type_env = (filter q (type_env new)) ++ (type_env old)
      , runtime_env = add (runtime_env new) (runtime_env old)
      }
 where p (x,y) = elem x vs
       q (str,tau,polyk) = elem (Global str) vs
       add (Ev xs _) (Ev ys t) = Ev (filter p xs ++ ys) t

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
           

       
       

multDef :: [Dec] -> [Var] -> FIO ()
multDef ds names = if null dups then return () else fail (foldr report "" dups)
  where dups = nub(names \\ nub names)
        locs = concat(map decloc ds)
        report :: Var -> String -> String
        report nm s = show nm ++ " is multiply defined at lines "++show (foldr acc [] locs)++"\n"++s
            where acc (name,SrcLoc line col) ls = if nm==name then line:ls else ls
                  acc (name,Z) ls = ls

-----------------------------------------------------
-- this command is for the maintainers of Omega, it trys
-- to load all the files in the TestPrograms directory with
-- extension ".prg"   It is used to exercise Omega.

alltests = 
  do { setCurrentDirectory "./TestPrograms"
     ; files <- getDirectoryContents "."
     ; let ok x = case reverse x of { ('g':'r':'p':'.':_) -> True; _ -> False}
     ; print (filter ok files)
     ; mapM try_to_load (filter ok files)
     ; setCurrentDirectory ".."
     }

-------------------------------------------------------------------------------
------------------------------------------------------------------
-- Some shortcuts to running the interpreter

work = run "work.prg"
circ = run "Examples/RecursiveCircuit.prg"
parse = run "Examples/Parser.prg"

tests = go "tests.prg"

tm = go "toMetaMl.prg"

q s = go ("C:/tmp/OmegaExamples/"++s++".prg")
