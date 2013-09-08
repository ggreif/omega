{-# LANGUAGE ViewPatterns, FlexibleContexts, FlexibleInstances
           , GADTs, MultiParamTypeClasses #-}

module ParserAll
  ( module Text.Parsec.Combinator
  , module Text.Parsec.Prim
  , module Text.Parsec.Char
  , module Text.Parsec.Expr
  , module TokenDef
  , Identity, natNoSpace
  , lexeme, comma, symbol, semi, whiteSpace, ident, construct, decimal
  , natural, identifier, parens, squares, braces, reserved, reservedOp
  , possible, parse2, integer, charLiteral, stringLiteral
  , layout, sourceName, sourceLine, sourceColumn, float, naturalOrFloat
  , isReservedName, prefixIdentifier, parseFromFile, opLetter, operator
  , oper, parseFromHandle, getPosition, Parser
  ) where

-- Note to use this module, the modules CommentDef.hs and TokenDef.hs
-- must exist usually in the same directory as the file that imports
-- ParserAll

import Text.Parsec.Combinator
import Text.Parsec.Prim hiding (Ok, getPosition, setPosition, runParser)
import Text.Parsec.Error
import qualified Text.Parsec.Prim as Prim
import Text.Parsec.Char
import qualified Text.Parsec.Token as P
import qualified Text.Parsec.Language as P
import Text.Parsec.Expr
import qualified Text.Parsec.Pos as Pos
import TokenDef
import Data.Functor.Identity
import System.IO (hGetContents, Handle)
import Unsafe.Coerce (unsafeCoerce)
import Control.Monad (guard)

nat = zeroNumber <|> decimal

zeroNumber = do { char '0'
                ; hexadecimal <|> octal <|> decimal <|> return 0
                } <?> ""

natNoSpace :: Parsec (Layout String Identity) u Int
natNoSpace = fmap fromInteger nat

relax :: Stream s Identity Char => (P.LanguageDef u, P.GenLanguageDef s u Identity) -> P.GenLanguageDef s u Identity
relax = unsafeCoerce fst

omegaTokens :: P.GenTokenParser (Layout String Identity) u Identity
omegaTokens = P.makeTokenParser tokenDef'

tokenDef'' :: Stream s Identity Char => P.GenLanguageDef s u Identity
tokenDef'' = (relax (tokenDef, undefined))
               { P.identStart = letter -- these do not cast benignly :-(
               , P.identLetter = alphaNum <|> oneOf "_'"
               , P.opStart = opLetters
               }
   where opLetters = oneOf ":!#$%&*+./<=>?@\\^|-~"

tokenDef' = tokenDef'' { P.opLetter = P.opStart tokenDef' }

lexeme = P.lexeme omegaTokens
comma = P.comma omegaTokens
symbol = P.symbol omegaTokens
semi = P.semi omegaTokens
whiteSpace = P.whiteSpace omegaTokens
natural = P.natural omegaTokens
identifier = P.identifier omegaTokens
parens = P.parens omegaTokens
squares = P.squares omegaTokens
braces = P.braces omegaTokens
reserved = P.reserved omegaTokens
reservedOp' = P.reservedOp omegaTokens
integer = P.integer omegaTokens
charLiteral = P.charLiteral omegaTokens
stringLiteral = P.stringLiteral omegaTokens
hexadecimal = P.hexadecimal omegaTokens
decimal = P.decimal omegaTokens
octal = P.octal omegaTokens
float = P.float omegaTokens
naturalOrFloat = P.naturalOrFloat omegaTokens
opLetter = P.opLetter tokenDef'
operator = P.operator omegaTokens

ident = do { c <- P.identStart tokenDef'
           ; cs <- many (P.identLetter tokenDef')
           ; return (c:cs)
           } <?> "identifier"

construct = do { c <- upper
               ; cs <- many (P.identLetter tokenDef')
               ; return (c:cs)
               } <?> "constructor name"

possible p = fmap Just (try p) <|> return Nothing

runParser :: Parser a -> String -> Maybe a
runParser = undefined4

unitState :: Parsec s u a -> Parsec s () a
unitState = unsafeCoerce

parse2 :: Parsec (Layout String Identity) u p -> String -> Either String (p, String)
parse2 p input
    = case runP (unitState (whiteSpace >> p)) () "keyboard input" (intoLayout input) of
        Left err -> Left (show err)
        Right p -> Right (p, "")

--------------------------------------------
-- Haskell style combinators

-- see http://stackoverflow.com/questions/3023439/parsing-indentation-based-syntaxes-in-haskells-parsec/3023615#3023615
-- and the resulting package: https://github.com/luqui/parsec-layout

layoutSep :: ParsecT (Layout String Identity) u Identity ()
layoutSep = virtualSep <?> "inserted layout separator (;)"
layoutEnd :: ParsecT (Layout String Identity) u Identity ()
layoutEnd = virtualEnd <?> "inserted layout closing brace"
layoutBegin = symbol "{" <?> "layout opening brace"
explicitBrace = symbol "}" <?> "explicit layout closing brace"

data SourcePos  = SourcePos { sourceName :: Pos.SourceName, sourceLine :: Pos.Line, sourceColumn :: Pos.Column }
    deriving (Eq, Ord)

getPosition :: Parsec (Layout String Identity) u SourcePos
getPosition = do (sourceParts -> (cs, line, col)) <- Prim.getPosition
                 return $ SourcePos cs line col
    where sourceParts s = (Pos.sourceName s, Pos.sourceLine s, Pos.sourceColumn s)

align p stop =
  do { x <- p
     ; whiteSpace
     ; (do { try layoutSep; xs <- align p stop; return (x:xs)}) <|>
       (do { try layoutEnd; stop; return [x]}) <|>
           -- removing indentation happens automatically
           -- while consuming 'virtualEnd'
       (do { stop; undent; return [x]})
     }

layout p stop =
  (do { try layoutBegin; xs <- P.semiSep omegaTokens p
      ; explicitBrace; stop; return xs}) <|>
  (do { indent; xs <- align p stop; return xs})


isReservedName = (`elem` P.reservedNames tokenDef')

oper = do { c <- (P.opStart tokenDef')
          ; cs <- many (P.opLetter tokenDef')
          ; return (c:cs)
          } <?> "operator"

reservedOp op = reservedOp' op >> return op

undefined4 = error "undefined4"

parseFromFile :: Parsec (Layout String Identity) u a -> Pos.SourceName -> IO (Either ParseError a)
parseFromFile p fname
    = do { input <- readFile fname
         ; return (runP (unitState p) () fname $ intoLayout input)
         }

parseFromHandle :: Parsec (Layout String Identity) u a -> Pos.SourceName -> Handle -> IO (Either ParseError a)
parseFromHandle p fname h
    = do { input <- hGetContents h
         ; return (runP (unitState p) () fname $ intoLayout input)
         }

prefixIdentifier c =
    lexeme $ try $
    do { char c
       ; name <- ident
       ; if (isReservedName name)
           then unexpected ("reserved word " ++ show name)
           else return name
       }

type Parser a = Parsec (Layout String Identity) () a


-- Layout Streams

data Layout s m where
  Indent :: (Monad m, Stream s m Char) => ![Int] -> !Int -> !Bool -> s -> Layout s m

class Stream s m t => LayoutStream s m t l where
  virtualSep :: ParsecT (l s m) u m ()
  virtualEnd :: ParsecT (l s m) u m ()
  indent :: ParsecT (l s m) u m ()
  undent :: ParsecT (l s m) u m ()
  intoLayout :: s -> l s m
  outofLayout :: l s m -> s

instance Stream s m Char => LayoutStream s m Char Layout where
  intoLayout = Indent [] 0 False
  outofLayout (Indent _ _ _ s) = s
  indent = do Indent tabs col c'ed s <- getInput
              setInput $ Indent (col:tabs) col True s
  undent = do Indent (_:tabs) col c'ed s <- getInput
              setInput $ Indent tabs col False s
  virtualSep = do Indent tabs@(tab:_) col False s <- getInput
                  guard $ col == tab
                  setInput $ Indent tabs col True s
  virtualEnd = do Indent (tab:out) col False s <- getInput
                  guard $ col < tab
                  setInput $ Indent out col False s


-- are instances of @Stream@
--
instance Monad m => Stream (Layout String m) m Char where
  uncons (Indent tabs col c'ed s) = do un <- uncons s
                                       case un of
                                         Nothing -> return Nothing
                                         Just ('\t', s') -> let over = col + 8 in return $ Just ('\t', Indent tabs (over - over `mod` 8) False s')
                                         Just ('\n', s') -> return $ Just ('\n', Indent tabs 0 False s')
                                         Just (t, s') -> case (tabs, c'ed) of
                                                         ([], _) -> justAdvance -- deactivated layout
                                                         _ | notSpace t && otherWhiteSpace s -> justAdvance
                                                         ((tab:_), False) | notSpace t && col <= tab -> return Nothing
                                                         _ -> justAdvance
                                            where justAdvance = return $ Just (t, Indent tabs (col + 1) False s')
    where otherWhiteSpace s = case parse (P.whiteSpace P.haskell >> Prim.getPosition) "" s of
                              Right pos | not $ atStart pos -> True
                              _ -> False
          notSpace ' ' = False
          notSpace _ = True
          atStart pos = Pos.sourceLine pos == 1 && Pos.sourceColumn pos == 1
