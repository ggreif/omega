module TokenDef ( tokenDef, omegaTokenParser
                , TokenDef.identifier
                , TokenDef.braces
                , TokenDef.parens
                , TokenDef.reserved ) where

import Text.Parsec.Token
import Text.Parsec.Language

-- Reserved Stuff
--
omegaDef = haskellStyle
   { reservedNames = [ "let", "in", "case", "of", "data", "kind", "prop", "where"
                     , "type", "if", "then", "else", "deriving", "do"
                     , "circuit", "theorem"
                     , "forall", "exists", "Ex", "check", "lazy", "flag"
                     , "monad", "primitive", "unreachable", "import"
                     ]
   , reservedOpNames = reservedOpNames haskellDef ++
                       [ "[|", "|]"
                       , "[e|"
                       , "[d|"
                       , "[p|"
                       , "[t|"
                       ] 
   }

tokenDef = omegaDef

omegaTokenParser = makeTokenParser omegaDef

parens = Text.Parsec.Token.parens omegaTokenParser
braces = Text.Parsec.Token.braces omegaTokenParser
identifier = Text.Parsec.Token.identifier omegaTokenParser
reserved = Text.Parsec.Token.reserved omegaTokenParser
