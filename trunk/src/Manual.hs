module Manual where

import System.IO(openFile,hClose,IOMode(..),hPutStr,stdout)
import Data.Char(isAlpha,isDigit)

-- Parts of the manual are generated automatically from the
-- sources, by generating LaTex files by observing the
-- data structures of the Omega sources

import LangEval(vals)
import Syntax(metaHaskellOps)
import Infer(typeConstrEnv0,modes_and_doc,predefined)
import Commands(commands)
import RankN(Sigma,disp0,Exhibit(..),PolyKind(..))
import Version(version,buildtime)

-----------------------------------------
-- LaTex-Like macros

figure h body caption label =
  do { hPutStr h "\\begin{figure}[t]\n"
     ; body
     ; hPutStr h ("\\caption{"++caption++"}\\label{"++label++"}\n")
     ; hPutStr h "\\hrule\n"
     ; hPutStr h "\\end{figure}\n"
     }

figure2 h body caption label =
  do { hPutStr h "\\begin{figure}[t]\n"
     ; hPutStr h "\\begin{multicols}{2}\n"
     ; body
     ; hPutStr h "\\end{multicols}\n"
     ; hPutStr h ("\\caption{"++caption++"}\\label{"++label++"}\n")
     ; hPutStr h "\\hrule\n"
     ; hPutStr h "\\end{figure}\n"
     }

verbatim h body =
 do { hPutStr h "{\\small\n\\begin{verbatim}\n"
    ; hPutStr h body
    ; hPutStr h "\\end{verbatim}}\n"
    }

itemize f h items =
  do { hPutStr h "\\begin{itemize}\n"
     ; mapM (\ x -> hPutStr h "\\item\n" >> f x >> hPutStr h "\n") items
     ; hPutStr h "\\end{itemize}\n"
     }


---------------------------------------------------------------------
-------------------------------------------------------------------
-- Printing out tables for the manual

vals' = map (\(name,maker) -> (name,maker name)) vals

infixOperators = (concat (map f metaHaskellOps))
  where f x = case lookup x vals' of
                 Nothing -> []
                 Just (_,y) -> [(x,showSigma y)]

main2 = makeManual "d:/Omega/doc"


makeManual :: String -> IO()
makeManual dir = go
  where kindfile = dir ++ "/kinds.tex"
        prefixfile = dir ++ "/infix.tex"
        comfile = dir ++ "/commands.tex"
        modefile = dir ++ "/modes.tex"
        prefile = dir ++ "/predef.tex"
        versionfile = dir ++ "/version.tex"
        licenseSrc = "../LICENSE.txt"
        licensefile = dir ++ "/license.tex"
        go = do { putStrLn "Writing tables for Manual"
                ; h <- openFile kindfile WriteMode
                ; predefinedTypes h
                ; hClose h

                ; h <- openFile prefixfile WriteMode
                ; prefixOp h
                ; hClose h

                ; h <- openFile comfile WriteMode
                ; command h
                ; hClose h

                ; h <- openFile modefile WriteMode
                ; modes h
                ; hClose h

                ; h <- openFile prefile WriteMode
                ; verbatim h predefined
                ; hClose h
                
                ; h <- openFile versionfile WriteMode
                ; hPutStr h (version++"\\\\"++buildtime++"\\\\")
                ; hClose h
                
                ; h <- openFile licensefile WriteMode
                ; s <- readFile licenseSrc
                ; verbatim h s
                ; hClose h
                }


------------------------------------------------------
-- helper function

showSigma:: Sigma -> String
showSigma s = scan (snd(exhibit disp0 s))
showpoly (K lvs s) = showSigma s

scan ('f':'o':'r':'a':'l':'l':xs) = dropWhile g (dropWhile f xs)
  where f c = c /= '.'
        g c = c `elem` ". "
scan xs = xs



f ("unsafeCast",_) = ""
f ("undefined",_) = ""
f (x,(y,z)) = (g x ++ " :: " ++ showSigma z ++ "\n")
hf (x,y,z) = (g x ++ " :: " ++ showpoly z ++ "\n")
hg (x,y) = "("++x++") :: " ++ y ++ "\n"
g [] = []
g "[]" = "[]"
g (s@(c:cs)) | isAlpha c = s         -- normal names
             | c == '(' = s
             | True = "("++s++")"    -- infix operators

predefinedTypes h =
 do { figure2 h
       (verbatim h
          ("\nType :: Kind \n\n"++(concat (map hf typeConstrEnv0))))
       "Predefined types and their kinds."
       "types"
    ; figure2 h
       (verbatim h
          ("\nValue :: Type \n\n"++(concat (map f vals'))))
              "Predefined functions and values."
          "values"
    }

prefixOp h =
  figure2 h
     (verbatim h
        ("\nOperator :: Type \n\n"++(concat (map hg infixOperators))))
     "The fixed set of infix operators and their types."
     "infix"

command h =
   figure h (verbatim h commands)
     "Legal inputs to the command line interpreter."
     "commands"

modes h = itemize f h modes_and_doc
  where f (name,init,doc) = hPutStr h line
          where line = "{\\tt "++under name++"}. Initial value = {\\tt "++show init++"}. "++doc++"\n"

under [] = []
under ('_' : xs) = "\\_"++under xs
under (x:xs) = x: under xs
