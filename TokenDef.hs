-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Thu Mar  3 11:15:06 Pacific Standard Time 2005
-- Omega Interpreter: version 1.0

module TokenDef(tokenDef) where

import StdTokenDef
import CommentDef


stratusStyle = haskellStyle
   { commentEnd = cEnd
   , commentStart = cStart
   , commentLine = cLine
   , nestedComments = nestedC
   , reservedNames = ["let","case","in","of","data","kind", "where","splice"
                     ,"data","type","then","else","deriving","reify"
                     ,"forall","L","R","check","lazy","under","flag", "monad", "primitive"
                     , "mono"
                     --,"exp","dec","pat","match","clause","import"
                     ]
   , reservedOpNames= ["=","\\"
                      ,"[|","|]"
                      ,"[e|"
                      ,"[d|"
                      ,"[p|"
                      ,"[t|"
                      ]
   }

tokenDef = stratusStyle
