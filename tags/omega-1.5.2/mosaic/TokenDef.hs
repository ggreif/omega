module TokenDef ( tokenDef, omegaTokenParser
                , TokenDef.identifier
                , TokenDef.reserved
                , TokenDef.operator
                , TokenDef.reservedOp
                , TokenDef.charLiteral
                , TokenDef.stringLiteral
                , TokenDef.natural
                , TokenDef.integer
                , TokenDef.braces
                , TokenDef.parens ) where

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
operator = Text.Parsec.Token.operator omegaTokenParser
reservedOp = Text.Parsec.Token.reservedOp omegaTokenParser
charLiteral = Text.Parsec.Token.charLiteral omegaTokenParser
stringLiteral = Text.Parsec.Token.stringLiteral omegaTokenParser
natural = Text.Parsec.Token.natural omegaTokenParser
integer = Text.Parsec.Token.integer omegaTokenParser
