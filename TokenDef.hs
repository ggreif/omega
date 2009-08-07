
module TokenDef(tokenDef) where

import StdTokenDef
import CommentDef


stratusStyle = haskellStyle
   { commentEnd = cEnd
   , commentStart = cStart
   , commentLine = cLine
   , nestedComments = nestedC
   , reservedNames = ["let","case","in","of","data","kind","prop", "where","splice"
                     ,"type","then","else","deriving","reify"
                     ,"circuit", "theorem"
                     ,"forall","exists","Ex","check","lazy","under","flag"
                     , "monad", "primitive", "unreachable"
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
