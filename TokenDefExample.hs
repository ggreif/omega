-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Tue Apr 25 12:54:27 Pacific Daylight Time 2006
-- Omega Interpreter: version 1.2.1

module TokenDef(tokenDef) where


-- This is a sample TokenDef module. Usually one exists in the
-- same directory as the file that imports ParserAll

import StdTokenDef
import CommentDef


stratusStyle = haskellStyle
   { commentEnd = cEnd
   , commentStart = cStart
   , commentLine = cLine
   , nestedComments = nestedC
   , reservedNames = ["let","case","in","of","data","where"]
   , reservedOpNames= ["=","\\"]
   }

tokenDef = stratusStyle
