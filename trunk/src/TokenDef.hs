{-# LANGUAGE FlexibleContexts #-}

module TokenDef ( tokenDef, unitState ) where

import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec.Prim
import Text.Parsec.Char
import CommentDef
import Data.Functor.Identity
import Unsafe.Coerce (unsafeCoerce)

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

relax :: Stream s Identity Char => (LanguageDef u, GenLanguageDef s u Identity) -> GenLanguageDef s u Identity
relax = unsafeCoerce fst

unitState :: Parsec s u a -> Parsec s () a
unitState = unsafeCoerce

tokenDef' :: Stream s Identity Char => GenLanguageDef s u Identity
tokenDef' = (relax (omegaStyle, undefined))
               { identStart = letter -- these do not cast benignly :-(
               , identLetter = alphaNum <|> oneOf "_'"
               , opStart = opLetters
               }
   where opLetters = oneOf ":!#$%&*+./<=>?@\\^|-~"

tokenDef :: Stream s Identity Char => GenLanguageDef s u Identity
tokenDef = tokenDef' { opLetter = opStart tokenDef }
