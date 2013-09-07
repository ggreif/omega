{-# LANGUAGE ViewPatterns, FlexibleContexts, FlexibleInstances
           , GADTs, MultiParamTypeClasses #-}

module ParserAll
  ( module Text.Parsec.Combinator
  , module Text.Parsec.Prim
  , module Text.Parsec.Char
  , module Text.Parsec.Expr
  , module TokenDef
  , LayoutStream(..), Identity, natNoSpace
  , lexeme, comma, symbol, semi, whiteSpace, ident, construct, decimal
  , natural, identifier, parens, squares, braces, reserved, reservedOp
  , reservedOp', possible, parse2, integer, charLiteral, stringLiteral
  , layout, sourceName, sourceLine, sourceColumn, float, naturalOrFloat
  , isReservedName, prefixIdentifier, parseFromFile, opLetter, operator
  , oper, parseFromHandle, getPosition, setPosition, Parser --, runParser

, res

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
import Text.Parsec.Expr
--import qualified Text.Parsec.Pos (SourcePos(..), SourceName, Line, Column) as Pos
import qualified Text.Parsec.Pos as Pos
import TokenDef
import Data.Functor.Identity
import System.IO (hGetContents, Handle)
import Unsafe.Coerce (unsafeCoerce)
import Control.Monad (guard)

natNoSpace :: Parsec (Layout String Identity) u Int
natNoSpace = fmap fromInteger natural -- TODO: fmap fromInteger nat -- do not eat space!!!!

--relax :: Stream s Identity Char => (P.LanguageDef u -> P.GenTokenParser String u Identity) -> (P.GenLanguageDef s u Identity -> P.GenTokenParser s u Identity)
relax :: Stream s Identity Char => (P.LanguageDef u, P.GenLanguageDef s u Identity) -> P.GenLanguageDef s u Identity
relax = unsafeCoerce fst



----omegaTokens :: Stream (Layout String Identity) Identity Char => P.GenTokenParser s u Identity
omegaTokens :: P.GenTokenParser (Layout String Identity) u Identity
omegaTokens = P.makeTokenParser tokenDef' -- ---$ relax (tokenDef, undefined)

tokenDef' = relax (tokenDef, undefined)

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
reservedOp = P.reservedOp omegaTokens
integer = P.integer omegaTokens
charLiteral = P.charLiteral omegaTokens
stringLiteral = P.stringLiteral omegaTokens
decimal = P.decimal omegaTokens
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
               } <?> "Constructor name"

possible p = fmap Just (try p) <|> return Nothing

runParser :: Parser a -> String -> Maybe a
runParser = undefined4

unitState :: Parsec (ParserAll.Layout String Identity) u a -> Parsec (ParserAll.Layout String Identity) () a
unitState = unsafeCoerce

unitState' :: Parsec s u a -> Parsec s () a
unitState' = unsafeCoerce

-----parse2 :: Stream s Identity Char => Parsec s u p -> u -> Either String (p, String)
parse2 :: Parsec (Layout String Identity) u p -> String -> Either String (p, String)
parse2 p input
    = case runP (unitState' (whiteSpace >> p)) () "keyboard input" (intoLayout input) of
        Left err -> Left (show err)
        Right p -> Right (p, "")

--        Ok x (State cs _ _) _ -> Right (x, cs)
--        Error err -> Left (show err)

{-
parserReply result
    = case result of
        Consumed reply -> reply
        Empty reply -> reply
-}

--------------------------------------------
-- Haskell style combinators

-- see http://stackoverflow.com/questions/3023439/parsing-indentation-based-syntaxes-in-haskells-parsec/3023615#3023615
-- and the resulting package: https://github.com/luqui/parsec-layout

layoutSep   = symbol ";" <?> "inserted layout separator (;)"
layoutEnd   = symbol "}" <?> "inserted layout closing brace"
layoutBegin = symbol "{" <?> "layout opening brace"
explicitBrace = symbol "}" <?> "explicit layout closing brace"

data SourcePos  = SourcePos { sourceName :: Pos.SourceName, sourceLine :: Pos.Line, sourceColumn :: Pos.Column, layoutTabs :: [Pos.Column] }
    deriving (Eq, Ord)

getPosition = do (sourceParts -> (cs, line, col)) <- Prim.getPosition
                 return $ SourcePos cs line col []
    where sourceParts s = (Pos.sourceName s, Pos.sourceLine s, Pos.sourceColumn s)

setPosition (SourcePos cs line col tabs) = Prim.setPosition $ Pos.newPos cs line col

indent :: Parsec s u ()
indent =
  do { SourcePos cs line col tabs <- getPosition
     ; setPosition (SourcePos cs line col (col : tabs))
     }

undent :: Parsec s u ()
undent =
  do { SourcePos cs line col (p:ps) <- getPosition
     ; setPosition (SourcePos cs line col ps)
     }

--align :: Parsec [Char] u a -> Parsec [Char] u b -> Parsec [Char] u [a]
align p stop =
  do { x <- p
     ; whiteSpace
     ; (do { try layoutSep; xs <- align p stop; return (x:xs)}) <|>
       (do { try layoutEnd; stop; return [x]}) <|>
           -- removing indentation happens automatically
           -- in function "update" (in Parser.hs), if we see layoutEnd
       (do { stop; undent; return [x]})
     }

--layout :: Parser a -> Parser b -> Parser [a]
--layout :: Parsec [Char] u a -> Parsec [Char] u b -> Parsec [Char] u [a]
layout p stop =
  (do { try layoutBegin; xs <- P.semiSep omegaTokens p
      ; explicitBrace; stop; return xs}) <|>
  (do { indent; xs <- align p stop; return xs})


isReservedName = (`elem` P.reservedNames tokenDef')

oper = do { c <- (P.opStart tokenDef')
          ; cs <- many (P.opLetter tokenDef')
          ; return (c:cs)
          } <?> "operator"

reservedOp' op = reservedOp op >> return op

undefined1 = error "undefined1"
undefined2 = error "undefined2"
undefined3 = error "undefined3"
undefined4 = error "undefined4"
undefined5 = error "undefined5"

parseFromFile :: Parsec (Layout String Identity) u a -> Pos.SourceName -> IO (Either ParseError a)
parseFromFile p fname
    = do { input <- readFile fname
         ; return (runP (unitState' p) () fname $ intoLayout input)
         }

parseFromHandle :: Parsec (Layout String Identity) u a -> Pos.SourceName -> Handle -> IO (Either ParseError a)
parseFromHandle p fname h
    = do { input <- hGetContents h
         ; return (runP (unitState' p) () fname $ intoLayout input)
         }
--parseFromHandle :: t -> u -> u -> IO (Either String b)
--parseFromHandle = undefined

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
  indent' :: ParsecT (l s m) u m ()
  intoLayout :: s -> l s m
  outofLayout :: l s m -> s

instance Stream s m Char => LayoutStream s m Char Layout where
  intoLayout = Indent [] 0 False
  outofLayout (Indent _ _ _ s) = s
  indent' = do (Indent tabs col c'ed s) <- getInput
               setInput $ Indent (col:tabs) col True s
  virtualSep = do (Indent tabs@(tab:_) col False s) <- getInput
                  guard $ col == tab
                  setInput $ Indent tabs col True s
  virtualEnd = do (Indent (tab:out) col False s) <- getInput
                  guard $ col < tab
                  setInput $ Indent out col False s


instance (Monad m, Stream s m Char) => Stream (Layout s m) m Char where
  uncons (Indent tabs col c'ed s) = do un <- uncons s
                                       case un of
                                         Nothing -> return Nothing
                                         Just ('\t', s') -> let over = col + 8 in return $ Just ('\t', Indent tabs (over - over `mod` 8) False s')
                                         Just ('\n', s') -> return $ Just ('\n', Indent tabs 0 False s')
                                         Just (t, s') -> case (tabs, c'ed) of
                                                         ((tab:_), False) | t /= ' ' && col == tab -> return Nothing
                                                         _ -> return $ Just (t, Indent tabs (col + 1) False s')

{-
 a = let
  b = id
   1
  c = 2 in b
 f = 3
 
 3 = let in 6
-}

inp :: Layout String Identity
inp = intoLayout " a = let\n  b = id\n   1\n  c = 2 in b\n f = 3\n \n 3 = let in 6\n"

lexeme' p = do good <- p ; many (oneOf " \n\t"); return good
identifier' = lexeme' (many1 $ oneOf "abcdi")
num' = lexeme' (many1 $ oneOf ['0' .. '9'])
prgm  = space >> identifier' >> lexeme' (string "= let") >> indent' >> virtualSep >> identifier'
prgm' = space >> identifier' >> lexeme' (string "= let") >> indent'
              >> identifier' >> lexeme' (string "=") >> identifier' >> num'
              >> virtualSep >> lexeme' identifier'

res,res' :: Either ParseError String
res = parse prgm "<inp>" inp

res' = parse prgm' "<inp>" inp
