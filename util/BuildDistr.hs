module BuildDistr  where

import Directory(doesFileExist,doesDirectoryExist,removeFile,
                 getCurrentDirectory,setCurrentDirectory,
                 getDirectoryContents)
import System.Directory(createDirectoryIfMissing)
import System(system)
import Time(getClockTime,toCalendarTime,calendarTimeToString)
import BuildSpecific( distrDir, srcDir, utilDir, parseDir, libDir
                    , manualDir, testsDir, rootDir, extension, version)
import System.IO.Unsafe(unsafePerformIO)

license =
 "-- Copyright (c) 2002-2011, Tim Sheard\n" ++
 "-- OGI School of Science & Engineering, Oregon Health & Science University\n" ++
 "-- Maseeh College of Engineering, Portland State University\n" ++
 "-- Subject to conditions of distribution and use; see LICENSE.txt for details.\n"
---------------------------------------------------------------------

sources =
 [ (libDir, "Auxillary", ".hs"),
   (libDir, "Bind", ".hs"),
   (libDir, "DepthFirstSearch", ".hs"),
   (libDir, "Monads", ".hs"),
   (libDir, "SCC", ".hs"),

   (parseDir, "StdTokenDef", ".hs"),
   (parseDir, "ParseError", ".hs"),
   (parseDir, "ParseExpr", ".hs"),
   (parseDir, "Parser", ".hs"),
   (parseDir, "ParserAll", ".hs"),
   (parseDir, "ParseToken", ".hs"),
   (parseDir, "TokenDefExample", ".hs"),
   (parseDir, "CommentDefExample", ".hs"),

   (srcDir, "ParserDef", ".hs"),
   (srcDir, "PrimParser", ".hs"),
   (srcDir, "CommentDef", ".hs"),
   (srcDir, "Encoding", ".hs"),
   (srcDir, "Infer", ".hs"),
   (srcDir, "LangEval", ".hs"),
   (srcDir, "Main", ".hs"),
   (srcDir, "RankN", ".hs"),
   (srcDir, "Syntax", ".hs"),
   (testsDir, "tests", ".prg"),
   (srcDir, "TokenDef", ".hs"),
   (srcDir, "Toplevel", ".hs"),
   (srcDir, "Value", ".hs"),
   (srcDir, "Manual", ".hs"),
   (srcDir, "Commands", ".hs"),
   (srcDir, "Narrow", ".hs"),
   (srcDir, "NarrowData", ".hs"),
   (srcDir, "Cooper", ".hs"),
   (srcDir, "SyntaxExt", ".hs"),
   (srcDir, "PureReadline",".hs"),
   (srcDir, "Version", ".hs"),

   (srcDir, "LangPrelude", ".prg"),
   (rootDir, "LICENSE", ".txt"),
   (srcDir, "Makefile",""),
   (utilDir, "omega",".cabal"), 
   (utilDir, "Setup",".hs")
 ]


-- ====================================================================
-- Create the target directory if it doesn't exist, if it does then
-- remove all the files there to get ready to move new versions there

ifM :: Monad m => m Bool -> m b -> m b -> m b
ifM test x y = do { b <- test; if b then x else y }


pwd = do { current <- getCurrentDirectory; putStrLn current}
cd s = setCurrentDirectory s

cleanTarget =
  ifM (doesDirectoryExist distrDir)
      (do { current <- getCurrentDirectory
          ; setCurrentDirectory distrDir
          ; allfiles <- getDirectoryContents distrDir
          ; let files = drop 2 allfiles -- remove . and .. from list
                f s = removeFile s
          ; putStr (show files)
          ; mapM f files
          ; setCurrentDirectory current
          })
      (createDirectoryIfMissing True distrDir)


getTime =
  do { clockt <- getClockTime
     ; calendart <- toCalendarTime clockt
     ;let shave (' ':xs) = shave xs
          shave ('\n':xs) = shave xs
          shave xs = xs
     ; return(shave(calendarTimeToString calendart))
     }


prepend time license source2path targetpath =
  do { writeFile targetpath (license ++ "-- " ++ time ++ "\n-- " ++ version ++ "\n\n")
     ; source2String <- readFile source2path
     ; appendFile targetpath source2String
     }

copyfile source target =
 do { string <- readFile source
    ; writeFile target string
    }


verbatimFile source target =
 do { string <- readFile source
    ; writeFile target ("\\begin{verbatim}\n" ++ string ++ "\\end{verbatim}\n")
    }

move1file time (dir, name, typ@".txt") =
   copyfile (dir ++ name ++ typ) (distrDir ++ "/" ++ name ++ typ)
move1file time (dir, name, typ@".cabal") =
   copyfile (dir ++ name ++ typ) (distrDir ++ "/" ++ name ++ typ)
move1file time (dir, name, typ@".ps") =
   system ("cp " ++ dir ++ name ++ typ ++ " " ++ distrDir ++ name ++ typ) >> return ()
move1file time (dir, name, typ@".pdf") =
   system ("cp " ++ dir ++ name ++ typ ++ " " ++ distrDir ++ name ++ typ) >> return ()
move1file time (dir, name, "") =
   copyfile (dir ++ name) (distrDir ++ "/" ++ name)
move1file time (dir, name, typ) =
    prepend time license
            (dir ++ name ++ typ) (distrDir ++ "/" ++ name ++ typ)

compile dir =
  do { setCurrentDirectory dir
     ; system "which ghc"
     ; system ("make EXT=" ++ extension)
     }

writeVersionInfo time =
  do { let versionfile = srcDir ++ "Version.hs"
           body = "module Version where\n" ++
                  "version = \"" ++ version ++ "\"\n" ++
                  "buildtime = \"" ++ time ++ "\"\n"
     ; writeFile versionfile body
     }


manuals =
 [ (manualDir, "OmegaManual", ".ps"),
   (manualDir, "OmegaManual", ".pdf")
 ]

makeManual dir time =
  do { system ("make -C " ++ dir ++ " manual EXT=" ++ extension)
     ; mapM (move1file time) manuals 
     }

main =
  do { system ("make -C " ++ srcDir ++ " update")
     ; time <- getTime
     ; putStr time
     ; cleanTarget
     ; writeVersionInfo time
     ; mapM (move1file time) sources
     ; makeManual srcDir time -- compiles, calls omega -manual, and then LaTeX
     ; setCurrentDirectory distrDir
     ; system "make clean"
     ; putStr ("\n" ++ version ++ "\n" ++ time ++ "\n")
     ; putStr ("Target Directory:  " ++ distrDir ++ "\n")
     ; putStr ("Root Directory:    " ++ rootDir ++ "\n")
     ; putStr ("Source Directory:  " ++ srcDir ++ "\n")
     ; putStr ("Parse Directory:   " ++ parseDir ++ "\n")
     ; putStr ("Library Directory: " ++ libDir ++ "\n")
     }


