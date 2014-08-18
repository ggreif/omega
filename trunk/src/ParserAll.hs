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
  , oper, parseFromHandle, getPosition, Parser, runParser
  ) where

-- Note to use this module, the modules CommentDef.hs and TokenDef.hs
-- must exist usually in the same directory as the file that imports
-- ParserAll

import Text.Parsec.Combinator
import Text.Parsec.Prim hiding (Ok, getPosition, setPosition, runParser)
import Text.Parsec.Error
import qualified Text.Parsec.Prim as P
import Text.Parsec.Char
import qualified Text.Parsec.Token as P
import qualified Text.Parsec.Language as P
import Text.Parsec.Expr
import qualified Text.Parsec.Pos as Pos
import TokenDef
import Data.Functor.Identity
import System.IO (hGetContents, Handle)
import Control.Monad (guard)
--import Debug.Trace

nat = zeroNumber <|> decimal

zeroNumber = do { char '0'
                ; hexadecimal <|> octal <|> decimal <|> return 0
                } <?> ""

natNoSpace :: Parsec (Layout String Identity) u Int
natNoSpace = fmap fromInteger nat


tokenDef' :: P.GenLanguageDef (Layout String Identity) u Identity
tokenDef' = tokenDef

omegaTokens :: P.GenTokenParser (Layout String Identity) u Identity
omegaTokens = P.makeTokenParser tokenDef'

lexeme p = suspendLayout $ P.lexeme omegaTokens p
comma = P.comma omegaTokens
symbol p = suspendLayout $ P.symbol omegaTokens p
semi = P.semi omegaTokens
whiteSpace = suspendLayout $ P.whiteSpace omegaTokens
natural = P.natural omegaTokens
identifier = P.identifier omegaTokens
parens = P.parens omegaTokens
squares = P.squares omegaTokens
braces = P.braces omegaTokens
reserved = P.reserved omegaTokens
reservedOp' = P.reservedOp omegaTokens
integer = P.integer omegaTokens
charLiteral = P.charLiteral omegaTokens
stringLiteral = suspendLayout $ P.stringLiteral omegaTokens
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
runParser p s = case runP (unitState p) () "<internal>" $ intoLayout s of
                Right res -> Just res
                _ -> Nothing

parse2 :: Parsec (Layout String Identity) u p -> String -> Either String (p, String)
parse2 p input
    = case runP (unitState (do whiteSpace; result <- p; eof; return result)) () "keyboard input" (intoLayout input) of
        Left err -> Left (show err)
        Right p -> Right (p, "")

--------------------------------------------
-- Haskell style combinators

-- see http://stackoverflow.com/questions/3023439/parsing-indentation-based-syntaxes-in-haskells-parsec/3023615#3023615
-- and the resulting package: https://github.com/luqui/parsec-layout
-- There are other attempts to indentation-aware parsing such as
--  - https://hackage.haskell.org/package/indentation
--        possibly explained here: http://michaeldadams.org/papers/layout_parsing/LayoutParsing.pdf
--        (see also Haskell Symposium paper 2014)
--  - http://hackage.haskell.org/package/indents

layoutSep :: Parsec (Layout String Identity) u ()
layoutSep = (virtualSep <?> "inserted layout separator") <|> (semi >> return ())
layoutEnd :: Parsec (Layout String Identity) u ()
layoutEnd = virtualEnd <?> "inserted layout closing brace"
layoutBegin = symbol "{" <?> "layout opening brace"
explicitBrace = symbol "}" <?> "explicit layout closing brace"

data SourcePos  = SourcePos { sourceName :: Pos.SourceName, sourceLine :: Pos.Line, sourceColumn :: Pos.Column }
    deriving (Eq, Ord)

getPosition :: Parsec (Layout String Identity) u SourcePos
getPosition = do (sourceParts -> (cs, line, col)) <- P.getPosition
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
          ; cs <- many opLetter
          ; return (c:cs)
          } <?> "operator"

reservedOp op = reservedOp' op >> return op

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
  Comment :: Stream s m Char => ![Int] -> !Int -> !Int -> s -> Layout s m
  Indent :: Stream s m Char => ![Int] -> !Int -> !Bool -> s -> Layout s m

class Stream s m t => LayoutStream s m t l where
  virtualSep :: ParsecT (l s m) u m ()
  virtualEnd :: ParsecT (l s m) u m ()
  indent :: ParsecT (l s m) u m ()
  undent :: ParsecT (l s m) u m ()
  suspendLayout :: ParsecT (l s m) u m a -> ParsecT (l s m) u m a
  intoLayout :: s -> l s m
  outofLayout :: l s m -> s
  otherWhiteSpace :: l s m -> s -> m (Maybe (s -> l s m))

-- Minor Hack:

genHaskellDef :: P.GenLanguageDef s u Identity
genHaskellDef = P.LanguageDef { P.commentStart   = P.commentStart P.haskellDef
                              , P.commentEnd     = P.commentEnd P.haskellDef
                              , P.commentLine    = P.commentLine P.haskellDef
                              , P.nestedComments = P.nestedComments P.haskellDef
                              , P.identStart = undefined, P.identLetter = undefined
                              , P.opStart = undefined , P.opLetter = undefined
                              , P.reservedNames = P.reservedNames P.haskellDef
                              , P.reservedOpNames = P.reservedOpNames P.haskellDef
                              , P.caseSensitive = P.caseSensitive P.haskellDef }

genHaskell :: Stream s Identity Char => P.GenTokenParser s u Identity
genHaskell = P.makeTokenParser genHaskellDef


instance Stream s Identity Char => LayoutStream s Identity Char Layout where
  intoLayout = Indent [] 0 False
  outofLayout (Indent _ _ _ s) = s
  indent = do Indent tabs col c'ed s <- getInput
              setInput $ Indent (col:tabs) col True s
  undent = do Indent (_:tabs) col c'ed s <- getInput
              setInput $ Indent tabs col False s
  suspendLayout p = p{-try (do Indent tabs col c'ed s <- getInput
                            setInput $ Indent [] col False s
                            at <- P.getPosition
                            traceShow ("DEACTIVATED! " ++ show tabs ++ show at) $ return ()
                            res <- p
                            Indent [] col c'ed s <- getInput
                            setInput $ Indent tabs col c'ed s
                            at <- P.getPosition
                            traceShow ("ACTIVATED! " ++ show tabs ++ show at) $ return ()
                            return res)-}
  virtualSep = do Indent tabs@(tab:_) col False s <- getInput
                  guard $ col == tab
                  setInput $ Indent tabs col True s
  virtualEnd = do Indent (tab:out) col False s <- getInput
                  guard $ col < tab
                  setInput $ Indent out col False s
  otherWhiteSpace (Indent tabs col _ _) s
                      = do p <- runParserT (P.whiteSpace genHaskell >> P.getPosition) () "" s
                           case p of
                             Right pos | not $ atStart pos
                               -> do Right skips <- runParserT (until pos 0) () "" s
                                     return $ Just $ Comment tabs skips (effCol pos)
                             _ -> return Nothing
    where atStart pos = Pos.sourceLine pos == 1 && Pos.sourceColumn pos == 1
          until pos n = do char' <- anyChar
                           pos' <- P.getPosition
                           if pos == pos' then return n else until pos $ 1 + n
          endCol 1 rcol = col + rcol
          endCol rlin rcol = rcol
          effCol pos = endCol (Pos.sourceLine pos) (Pos.sourceColumn pos) - 1

-- are instances of @Stream@
--
-- TODO: handle \r, See: r1843
--
instance (Monad m, LayoutStream s m Char Layout) => Stream (Layout s m) m Char where
  uncons (Comment tabs 0 col s) = error "should not happen!" -- uncons $ Indent tabs col False s
  uncons (Comment tabs n col s) = do un <- uncons s
                                     case (n, un) of
                                       (_, Nothing) -> return Nothing
                                       (_, Just ('\t', s')) -> error "TAB in comment? WTF to do?"
                                       (1, Just ('\n', s')) -> return $ Just ('\n', Indent tabs 0 False s')
                                       (1, Just (t, s')) -> return $ Just (t, Indent tabs col False s')
                                       (_, Just (t, s')) -> return $ Just (t, Comment tabs (n - 1) col s')
  uncons i@(Indent tabs col c'ed s) = do un <- uncons s
                                         case un of
                                           Nothing -> return Nothing
                                           Just ('\t', s') -> let over = col + 8 in return $ Just ('\t', Indent tabs (over - over `mod` 8) False s')
                                           Just ('\n', s') -> return $ Just ('\n', Indent tabs 0 False s')
                                           Just (t, s') -> case (tabs, c'ed) of
                                                           ([], _) -> justAdvance -- deactivated layout
                                                           conf | notSpace t -> do white <- otherWhiteSpace i s
                                                                                   case white of
                                                                                     Just ersatz -> return $ Just (t, ersatz s')
                                                                                     _ -> mayBlock conf
                                                           conf -> mayBlock conf
                                              where justAdvance = return $ Just (t, Indent tabs (col + 1) False s')
                                                    mayBlock ((tab:_), False) | notSpace t && col <= tab = return Nothing
                                                    mayBlock _ = justAdvance

notSpace ' ' = False
notSpace _ = True
