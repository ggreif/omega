module TokenDef ( tokenDef ) where

import Text.Parsec.Token
import Text.Parsec.Language
import CommentDef


omegaStyle = haskellStyle
   { commentEnd = cEnd
   , commentStart = cStart
   , commentLine = cLine
   , nestedComments = nestedC
   , reservedNames = [ "let", "in", "case", "of", "data", "kind", "prop", "where"
                     , "type", "if", "then", "else", "deriving", "do"
                     , "circuit", "theorem"
                     , "forall", "exists", "Ex", "check", "lazy", "flag"
                     , "monad", "primitive", "unreachable", "import"
                     ]
   , reservedOpNames= [ "=", "\\"
                      , "[|", "|]"
                      , "[e|"
                      , "[d|"
                      , "[p|"
                      , "[t|"
                      ]
   }

tokenDef = omegaStyle
