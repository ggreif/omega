module TokenDef(tokenDef) where

import StdTokenDef
import CommentDef


stratusStyle = haskellStyle
   { commentEnd = cEnd
   , commentStart = cStart
   , commentLine = cLine
   , nestedComments = nestedC
   , reservedNames = ["let","case","in","of","data","kind","prop","where"
                     ,"type","then","else","deriving"
                     ,"circuit", "theorem"
                     ,"forall","exists","Ex","check","lazy","under","flag"
                     , "monad", "primitive", "unreachable"
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
