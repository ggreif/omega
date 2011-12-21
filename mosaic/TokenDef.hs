module TokenDef ( tokenDef, omegaTokenParser
                , TokenDef.identifier ) where

import Text.Parsec.Token
import Text.Parsec.Language
--import StdTokenDef
--import CommentDef

-- Haskell Style Comments
--
cStart = "{-"   -- (commentStart tokenDef)
cEnd   = "-}"   -- (commentEnd tokenDef)
cLine  = "--"   -- (commentLine tokenDef)
nestedC = True  -- (nestedComment tokenDef)

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
   , reservedOpNames = [ "=", "\\"
                       , "[|", "|]"
                       , "[e|"
                       , "[d|"
                       , "[p|"
                       , "[t|"
                       ]
   }

tokenDef = omegaStyle

omegaTokenParser = makeTokenParser tokenDef

parens = Text.Parsec.Token.parens omegaTokenParser
braces = Text.Parsec.Token.braces omegaTokenParser
identifier = Text.Parsec.Token.identifier omegaTokenParser
reserved = Text.Parsec.Token.reserved omegaTokenParser
