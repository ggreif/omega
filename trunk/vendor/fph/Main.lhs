\begin{code}

module Main where 
import BasicTypes
import Parser
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec 


import IO (IOMode(..), openFile, hPutStrLn, hGetContents, stderr) 
import System (getArgs, exitWith, ExitCode(..)) 

import TcMonad 
import Wrappers 



initEnv :: IO TcEnv 
initEnv = createEnv [("+",(intType --> (intType --> intType)))]
                    [("Int",0)] 


main :: IO () 
main = do { args <- getArgs
          ; case args of 
              [] -> getContents >>= tcs
              [f] -> tcf f 
              _ -> do { hPutStrLn stderr "Usage: exec [FILE]"
                      ; exitWith (ExitFailure 1) } 
       } 

tcs:: String -> IO () 
tcs s = tc_help (parseString s) 

tcf :: String -> IO () 
tcf f = do { h <- openFile f ReadMode
           ; str <- hGetContents h 
           ; tc_help (parseString str) } 


parseFile :: String -> IO (Maybe [Decl])
parseFile filename
  = do { r <- parseFromFile parseDecls filename
       ; case r of
	   Left err -> do { putStrLn ("Parse error: " ++ show err) 
			    ; return Nothing }
	   Right ans -> return (Just ans) }

parseString :: String -> IO (Maybe [Decl])
parseString str
  = do { let r = parse parseDecls "<interactive>" str
       ; case r of
	   Left err -> do { putStrLn ("Parse error: " ++ show err) 
			    ; return Nothing }
	   Right ans -> return (Just ans) }


tc_help :: IO (Maybe [Decl]) -> IO () 
tc_help decls = 
   do { mb_ds <- decls 
      ; case mb_ds of 
          Nothing -> return () 
          Just ds -> 
--                       do { mapM (putStrLn.docToString.ppr) ds
--                          ; return (); } 

                       do { env <- initEnv 
                          ; res <- runTc env (tcDecls ds []) 
                          ; case res of 
                              Left msg -> putStrLn $ render msg
                              Right _ -> putStrLn "Success!" 
                          }

-- do { mapM (putStrLn.docToString.ppr) ds
--                         ; return (); } 

   }
                        

\end{code} 