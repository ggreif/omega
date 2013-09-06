{-# LANGUAGE RankNTypes #-}
module Toplevel where

import Data.Char(isAlpha,isDigit)
import Data.List(partition,(\\),nub,find,deleteBy,sort)
import Data.Map(Map,toList)
import System.IO

import Version(version,buildtime)
import Syntax
import ParserDef(getInt,pCommand,parseString,Command(..)
                ,program,parseHandle)
import LangEval(Env(..),env0,eval,elaborate,Prefix(..),mPatStrict,extendV)
import Monads(FIO(..),unFIO,runFIO,fixFIO,fio,resetNext
             ,write,writeln,readln,unTc,tryAndReport,fio,fioFailD
             ,errF,report,writeRef,handleP)
import Auxillary(plist,plistf,backspace,Loc(..),extendL,DispInfo,DispElem(..),eitherM)
import SCC(topSortR)
import Control.Monad(when)
import Infer(TcEnv(sourceFiles,tyfuns),completionEntry,lineEditReadln,initTcEnv
             ,mode0,modes,checkDecs,imports,addListToFM,appendFM2
             ,var_env,type_env,rules,runtime_env,syntaxExt)
import RankN(pprint,Z,failD,disp0,dispRef)
import Manual(makeManual)
import Commands
import SyntaxExt(synName,synKey)

import System.Environment(getArgs)
import Data.Time.Clock(UTCTime,getCurrentTime)
import System.IO(hClose)
import Control.Exception(try,IOException)
import System.FilePath(splitFileName)
import System.Directory(setCurrentDirectory,getDirectoryContents,getModificationTime)


-- import System.Console.Readline(setCompletionEntryFunction)
-- setCompletionEntryFunction :: Maybe (String -> IO [String]) -> IO ()

-------------------------------------------------------------
-- The programmer interface: the top level loop.
-- it performs the read-eval-typecheck-print loop.
-- It catches exceptions, and ties all the other pieces together.

----------------------------------------------
-- Perform one Read-Eval-Print action.

-- readEvalPrint :: [String] -> (TcEnv) -> FIO(TcEnv)
readEvalPrint commandTable sources tenv =
  do { let tabExpandFun = completionEntry tenv
           white c = elem c " \t\n"
     ; input <- lineEditReadln "prompt> " tabExpandFun
     ; z <- parseString pCommand input
     ; case z of
        Left s -> do {writeln s; return (tenv) }
        Right(x,rest) | all white rest ->
         case x of
          (ColonCom com str) -> dispatchColon commandTable tenv com str
          (ExecCom e) -> execExp tenv e
          (DrawCom p e) -> drawPatExp tenv p e
          (LetCom d) -> letDec elabDs tenv d
          (EmptyCom) -> return tenv
        Right(x,rest) -> fail ("\nI parsed the command:\n "++show x++
                               "\nBut there was some trailing text: "++rest)
     }


-- Repeat Read-Eval-Print until the :q command is given
topLoop commandTable sources env = tryAndReport
  (do { fio(hFlush stdout)
      ; fio(writeRef dispRef disp0)
      ; env' <-  (readEvalPrint commandTable sources init)
      ; topLoop commandTable (sourceFiles env') env'
      }) (report (topLoop commandTable (sourceFiles init) init))
 where init = (env{sourceFiles=sources})

------------------------------------------------------------------
-- Commands for load files, then going into the toplevel loop
------------------------------------------------------------------

-- load just the prelude and then go into the toplevel loop
main :: IO ()
main = runFIO(do { let sources = ["LangPrelude.prg"]
                 ; writeln ("Loading source files = "++show sources)
                 ; fio $ hSetBuffering stdout NoBuffering
                 ; fio $ hSetBuffering stdin  NoBuffering
                 ; (env1,time) <- 
                       tryAndReport (elabFile 0 "LangPrelude.prg" initTcEnv)
                                    (report (return(initTcEnv,undefined)))
                 ; let sources2 = sourceFiles env1
                 ; topLoop (commandF (elabFile 0)) sources2 env1
                 ; return () }) errF


-- Load the prelude and then load the file "s", and then go into the toplevel loop.
go :: String -> IO ()
go s =
  runFIO(do { writeln (version++"  --  Type ':?' for command line help."++"\n\n")
            ; let sources = ["LangPrelude.prg",s]
            ; writeln ("Loading source files = "++show sources)
            ; writeln "loading the prelude (LangPrelude.prg)"
            ; (env,time) <- tryAndReport (elabFile 0 "LangPrelude.prg" initTcEnv)
                                            (report (return (initTcEnv,undefined)))
            ; (env2,time2) <- elabFile 0 s env
            ; let sources2 = sourceFiles env2
            ; topLoop (commandF (elabFile 0)) sources2 env2
            ; return () }) errF


-- Don't load the prelude, just load "s" then go into the toplevel loop.
run :: String -> IO ()
run s = runFIO(do { let (dir,name) = splitFileName s
                  ; fio (when (not (null dir)) (setCurrentDirectory dir))
                  ; writeRef modes mode0
                  ; writeln ("Loading source files = "++show [s])
                  ; let init = (initTcEnv{sourceFiles = [s]})
                  ; (env1,time) <- tryAndReport (elabFile 0 s init)
                                                (report (return (init,undefined)))
                  ; let sources2 = sourceFiles env1
                  ; topLoop (commandF (elabFile 0)) sources2 env1
                  ; return () }) errF


-- Try to load a file, if it fails for any reason, exit the program
-- with an unrecoverable error. Used in testing, where failure means
-- a major error, something very bad (and unexpected), has happened
try_to_load s =
   runFIO(do { writeln ("loading "++s)
             ; (env1,time) <- tryAndReport (elabFile 0 s initTcEnv) err2
             ; writeln (s++" successfully loaded")
             ; return () }) errF
  where err2 loc mess = error ("At "++show loc++"\n"++mess)


-- Get the file to "run" from the command line arguments, then "run" it
omega :: IO()
omega =
  do { args <- getArgs
     ; putStr (version++"\n")
     ; putStr ("Build Date: "++buildtime++"\n\n")
     ; putStr "Type ':?' for command line help.\n"
     ; case args of
        [] -> run "LangPrelude.prg"
        ("-tests" : dir : _) -> alltests dir
        ("-manual" : dir : _) -> makeManual dir
        (file : _) -> run file
     }

-------------------------------------------------------------------------------
-- elabDs is the interface to everything. Elaborates a mutually recursive [Dec]
-- other functions read the [Dec] from files and call this function

elabDs :: [Dec] -> TcEnv -> FIO TcEnv
elabDs ds (tenv) =
  do { let nam (Global s) = s
     -- ; write ((display (map nam (concat (map decname ds))))++" ")
     ; (tenv1,ds1,cs1) <- checkDecs tenv ds   -- type check the list
     --; mapM (writeln .show) ds
     --; mapM (writeln . show) ds1
     ; when (not (null cs1))
            (fioFailD 3 disp0 [Ds "Unsolved constraints (type 2): ",Ds  (show cs1)])
     ; env1 <- elaborate None ds1 (runtime_env tenv)  -- evaluate the list
     ; return(tenv1 { runtime_env = env1 })
     }

display [s] = s
display ss = plistf id "(" ss " " ")"



------------------------------------------------------------------
-- Get a [Dec] from a file name

parseDecs :: String -> FIO [Dec]
parseDecs file =
  do { hndl <- eitherM (fio (try $ openFile file ReadMode))
                 (\ err -> fail ("\nProblem opening file: "++file++"  ("++show (err :: IOException)++")"))
                 return
     ; let err mess = fio (hClose hndl >> fail mess) -- if parsing fails, we should close the file
     ; x <- handleP (const True) 10
                    (fio $ parseHandle program file hndl) err
     ; fio (hClose hndl)
     ; case x of
        Left s -> fail s
        Right (Program ds) -> return ds
     }

-------------------------------------------------------------------------
-- Omega has a very simple importing mechanism. A user writes:
-- import "xx.prg" (f,g,T)
-- to import the file named "xx.prg", all symbols with names "f", "g", "T"
-- (no matter what namespace they appear in) are imported into the
-- current environment. Usually "xx.prg" is a complete path as Omega's
-- notion of current directory is quite primitive.
-- import "xx.prg"  means import everything from "xx.prg"

importP (Import s vs) = True
importP _ = False

importName (Import s vs) = s

------------------------------------------------------------
-- Read a [Dec] from a file, then split it into imports and
-- binding groups, uses elabDs to do the work.

indent n = replicate ((n-1)*3) ' '
nameOf (name,time,deps,env) = name
 
elabFile :: Int -> String -> TcEnv -> FIO(TcEnv, UTCTime)
elabFile count file (tenv) =
   do { time <- fio getCurrentTime
      ; all <- parseDecs file
      ; let (importL,ds) = partition importP all
            (dss,pairs) = topSortR freeOfDec ds
      ; writeln(indent count++"->Loading import "++basename file)
      ; (tenv2,importList) <- importManyFiles (count + 1) importL tenv      
      --; mapM (writeln . (++"\n"). show) ds
      --; writeln ("\nelaborating "++file++"\n"++show(map freeOfDec ds)++"\n pairs\n"++show pairs)
      -- Check for multiple definitions in the file
      ; multDef ds (concat (map fst pairs))
      -- Check if any names are already declared
      ; mapM (notDup tenv2 file) (foldr (\ (exs,deps) ss -> exs++ss) [] pairs)      
      ; tenv3 <- foldF elabDs (tenv2) dss
      ; let tenv4 = adjustImports file time importList tenv3
      ; writeln ((indent (count+1))++"<-"++file++" loaded.")
      ; return (tenv4,time)
      }

adjustImports name time deps new = new2 
  where -- a little recursive knot tying so the env being defined (new2) is
        -- also stored in the imports list of the function being added
        new2 = new {imports = m : (filter pred (imports new))}
        m = (name,time,deps,new2)
        keepers = map fst deps
        pred (nm1,time1,deps1,env1) = elem nm1 keepers
          

addI [] old = old
addI ((m@(nm,time,deps,env)):more) old = (nm,time,deps,env): (addI more (deleteBy same m old))
  where same (nm1,time1,deps1,env1) (nm2,time2,deps2,env2) = nm1 == nm2

lookupDeps nm env = case find match (imports env) of 
                        Nothing -> fail ("Unknown module when lokking up dependency list: "++nm)
                        Just(nm,time,deps,env) -> return deps
  where match (name,time,deps,env) = name==nm                        
 
showimp message env = message++plistf nameOf "(" (imports env) "," ")."

importManyFiles:: Int -> [Dec] -> TcEnv -> FIO (TcEnv, [(String, UTCTime)])
importManyFiles count [] tenv = return (tenv,[])
importManyFiles count (d:ds) tenv =
  do { (next,name,time) <- importFile count d tenv
     ; (next2,ts) <- importManyFiles count ds next
     ; return(next2,(name,time):ts) }

importFile :: Int -> Dec -> TcEnv -> FIO(TcEnv,String,UTCTime)
importFile count (Import name vs) tenv =
  case find (\(nm,time,deps,env)->name==nm) (imports tenv) of
     Just (nm,time,deps,env) -> 
                do { writeln (indent count++"Import "++name++" already loaded.")
                   ; return (importNames nm vs env tenv,nm,time) }
     Nothing -> do { (new,time) <- elabFile count name tenv 
                   ; deps <- lookupDeps name new
                   ; unknownExt vs (syntaxExt new)
                   ; let new2 = adjustImports name time deps new
                   ; return(importNames name vs new2 tenv,name,time) }

importNames :: String -> Maybe [ImportItem] -> TcEnv -> TcEnv -> TcEnv
importNames name items new old =
  old { imports = addI (imports new) (imports old)
      , var_env = addListToFM (var_env old) (filter okToAddVar (toList (var_env new)))
      , type_env = filter q (type_env new) ++ type_env old
      , runtime_env = add (runtime_env new) (runtime_env old)
      , rules = appendFM2 (rules old) (filter p2 (toList (rules new)))
      , syntaxExt = addSyntax syntax (syntaxExt new) (syntaxExt old)
      , tyfuns = filter okToAddTyFun (tyfuns new) ++ tyfuns old
      }
      
 where elemOf x Nothing = True          -- No import list, so everything is imported
       elemOf x (Just vs) = elem x vs   -- is it in the import list?
       okToAddVar :: forall a . (Var, a) -> Bool
       okToAddVar (x,y) = elemOf x vs
       okToAddTyFun (x,y) = elemOf (Global x) vs
       p2 (s,y) = elemOf (Global s) vs
       q (str,tau,polyk) = elemOf (Global str) vs
       add (Ev xs) (Ev ys) = Ev (filter okToAddVar xs ++ ys)
       accV (VarImport v) vs = v:vs  -- used to fold over the runtime environment
       accV _ vs = vs
       accSyn (SyntaxImport nm tag) vs = (nm,tag):vs -- fold over syntax imports
       accSyn _ vs = vs
       (vs,syntax) = case items of
             Just zs -> (Just(foldr accV [] zs),Just(foldr accSyn [] zs))
             Nothing -> (Nothing,Nothing)

addSyntax Nothing new old = new ++ old
addSyntax (Just imports) new old = foldr acc old new
  where acc ext old = if (synName ext,synKey ext) `elem` imports
                         then ext:old else old

unknownExt Nothing new = return ()
unknownExt (Just []) new = return ()
unknownExt (Just(VarImport x : xs)) new = unknownExt (Just xs) new
unknownExt (Just(SyntaxImport nm tag : xs)) new =
      if any good new
         then unknownExt (Just xs) new
         else fail ("\nImporting unknown extension: "++nm++"("++tag++")")
   where good ext = synName ext == nm && synKey ext == tag




multDef :: [Dec] -> [Var] -> FIO ()
multDef ds names = if null dups then return () else fail (foldr report "" dups)
  where dups = nub(names \\ nub names)
        locs = concat(map decloc ds)
        report :: Var -> String -> String
        report nm s = show nm ++ " is multiply defined at lines "++show (foldr acc [] locs)++"\n"++s
            where acc (name,SrcLoc _ line col) ls = if nm==name then line:ls else ls
                  acc (name,Z) ls = ls

-----------------------------------------------------
-- this command is for the maintainers of Omega, it tries
-- to load all the files in the TestPrograms directory with
-- extension ".prg"   It is used to exercise Omega.

alltests dir =
  do { setCurrentDirectory dir
     ; files' <- getDirectoryContents "."
     ; let ok x = case reverse x of { ('g':'r':'p':'.':_) -> True; _ -> False}
     ; let files = sort files'
     ; print (filter ok files)
     ; mapM try_to_load (filter ok files)
     ; setCurrentDirectory ".."
     }


-------------------------------------------------------------------------------
------------------------------------------------------------------
-- Some shortcuts to running the interpreter

work = run "work.prg"
ky = run "D:/IntelWork/Kyung2.prg"
bad = run "D:/work/sheard/research/omega/badPrograms/shaped.prg"
qq = run "d:/LogicBlox/Code/LogicMetaGenerator/Text/meaning.prg"

add = run "D:/IntelWork/adder.prg"

temp = run "D:/IntelWork/temp.prg"
circ = run "Examples/RecursiveCircuit.prg"
parse = run "Examples/Parser.prg"

tests = go "tests.prg"

tm = go "toMetaMl.prg"

q s = go ("C:/tmp/OmegaExamples/"++s++".prg")

