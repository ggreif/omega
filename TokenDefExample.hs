
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
