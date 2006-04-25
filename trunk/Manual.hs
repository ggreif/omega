-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Tue Apr 25 12:54:27 Pacific Daylight Time 2006
-- Omega Interpreter: version 1.2.1

module Manual where

import IO (openFile,hClose,IOMode(..),hPutStr,stdout)
import Char(isAlpha,isDigit)

-- Parts of the manual are generated automatically from the
-- sources, by generating LaTex files by observing the
-- data structures of the Omega sources

import LangEval(vals)
import Syntax(metaHaskellOps)
import Infer2(typeConstrEnv0,modes_and_doc,predefined)
import Commands(commands)

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

infixOperators = (concat (map f metaHaskellOps))
  where f x = case lookup x vals of
                 Nothing -> []
                 Just (_,y) -> [(x,show y)]

main2 = makeManual


makeManual :: IO()
makeManual = go
  where kindfile = "D:/work/papers/OmegaManual/kinds.tex"
        prefixfile = "D:/work/papers/OmegaManual/types.tex"
        comfile = "D:/work/papers/OmegaManual/commands.tex"
        modefile = "D:/work/papers/OmegaManual/modes.tex"
        prefile = "D:/work/papers/OmegaManual/predef.tex"
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
                }


------------------------------------------------------
-- helper function

f ("unsafeCast",_) = ""
f ("undefined",_) = ""
f (x,(y,z)) = (g x ++ " :: " ++ show z ++ "\n")
hf (x,y,z) = (g x ++ " :: " ++ show z ++ "\n")
hg (x,y) = "("++x++") :: " ++ show y ++ "\n"
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
          ("\nValue :: Type \n\n"++(concat (map f vals))))
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