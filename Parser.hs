-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Tue Jun 12 16:20:11 Pacific Daylight Time 2007
-- Omega Interpreter: version 1.4.2

{-----------------------------------------------------------
 Daan Leijen (c) 1999-2000, daan@cs.uu.nl

 $version: 23 Feb 2000, release version 0.2$

 Parsec, the Fast Monadic Parser combinator library.
 http://wwww.cs.uu.nl/~daan/parsec.html

 Inspired by:

    Graham Hutton and Erik Meijer:
    Monadic Parser Combinators.
    Technical report NOTTCS-TR-96-4.
    Department of Computer Science, University of Nottingham, 1996.
    http://www.cs.nott.ac.uk/Department/Staff/gmh/monparsing.ps

 and:

    Andrew Partridge, David Wright:
    Predictive parser combinators need four values to report errors.
    Journal of Functional Programming 6(2): 355-364, 1996
-----------------------------------------------------------}

module Parser(
             --operators: label a parser, alternative
               (<?>), (<|>)

             --basic types
             , Parser, parse, parseFromFile, parse2, skip
             , parseFromHandle, Handle

             , ParseError, errorPos, errorMessages
             , SourcePos(..), sourceName, sourceLine, sourceColumn
             , SourceName, Source, Line, Column
             , Message(SysUnExpect,UnExpect,Expect,Message)
             , messageString, messageCompare, messageEq, showErrorMessages

             --general combinators
             , skipMany, skipMany1
             , many, many1, manyTill
             , sepBy, sepBy1
             , count
             , chainr1, chainl1
             , option, optional
             , choice, between
             --, oneOf, noneOf
             , anySymbol
             , notFollowedBy

             --language dependent character parsers
             , letter, alphaNum, lower, upper, newline, tab
             , digit, hexDigit, octDigit
             , space, spaces
             , oneOf, noneOf
             , char, anyChar
             , string
             , eof
             , possible

             --primitive
             , satisfy
             , try
             , token                        --obsolete, use try instead
             , pzero, onFail, unexpected
             , getPosition, setPosition
             , getInput, setInput
             , getState, setState

             -- used to be in ParseToken
             , symbol, lexeme, whiteSpace
             ) where

import ParseError
import CommentDef
import Monad
import Char
import List(nub)
import System.IO(hGetContents,Handle)

-----------------------------------------------------------
-- Operators:
-- <?>  gives a name to a parser (which is used in error messages)
-- <|>  is the choice operator
-----------------------------------------------------------
infix  0 <?>
infixr 1 <|>


(<?>) :: Parser a -> String -> Parser a
p <?> msg           = onFail p msg

(<|>) :: Parser a -> Parser a -> Parser a
p1 <|> p2           = mplus p1 p2


-----------------------------------------------------------
-- Character parsers
-----------------------------------------------------------
spaces              = skipMany space       <?> "white space"
space               = satisfy (isSpace)     <?> "space"

newline             = char '\n'             <?> "new-line"
tab                 = char '\t'             <?> "tab"

upper               = satisfy (isUpper)     <?> "uppercase letter"
lower               = satisfy (isLower)     <?> "lowercase letter"
alphaNum            = satisfy (isAlphaNum)  <?> "letter or digit"
letter              = satisfy (isAlpha)     <?> "letter"
digit               = satisfy (isDigit)     <?> "digit"
hexDigit            = satisfy (isHexDigit)  <?> "hexadecimal digit"
octDigit            = satisfy (isOctDigit)  <?> "octal digit"


-- char c              = satisfy (==c)  <?> show [c]
char c              = do{ string [c]; return c}  <?> show [c]
anyChar             = anySymbol

-- string :: String -> Parser String
-- string is defined later as a primitive for speed reasons.


-----------------------------------------------------------
-- General parser combinators
-----------------------------------------------------------
noneOf cs           = satisfy (\c -> not (c `elem` cs))
oneOf cs            = satisfy (\c -> c `elem` cs)

anySymbol           = satisfy (const True)


choice :: [Parser a] -> Parser a
choice ps           = foldr (<|>) mzero ps

option :: a -> Parser a -> Parser a
option x p          = p <|> return x

optional :: Parser a -> Parser ()
optional p          = do{ p; return ()} <|> return ()

between :: Parser open -> Parser close -> Parser a -> Parser a
between open close p
                    = do{ open; x <- p; close; return x }


skipMany,skipMany1 :: Parser a -> Parser ()
skipMany1 p         = do{ p; skipMany p }
skipMany p          = scan
                    where
                      scan  = do{ p; scan } <|> return ()

many1,many :: Parser a -> Parser [a]
many1 p             = do{ x <- p; xs <- many p; return (x:xs) }

many p              = scan id
                    where
                      scan f    = do{ x <- p
                                    ; scan (\tail -> f (x:tail))
                                    }
                                <|> return (f [])

sepBy1,sepBy :: Parser a -> Parser sep -> Parser [a]
sepBy p sep         = sepBy1 p sep <|> return []
sepBy1 p sep        = do{ x <- p
                        ; xs <- many (sep >> p)
                        ; return (x:xs)
                        }

count :: Int -> Parser a -> Parser [a]
count n p           | n <= 0    = return []
                    | otherwise = sequence (replicate n p)


chainr p op x       = chainr1 p op <|> return x
chainl p op x       = chainl1 p op <|> return x

chainr1,chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op        = do{ x <- p; rest x }
                    where
                      rest x    = do{ f <- op
                                    ; y <- p
                                    ; rest (f x y)
                                    }
                                <|> return x

chainr1 p op        = scan
                    where
                      scan      = do{ x <- p; rest x }

                      rest x    = do{ f <- op
                                    ; y <- scan
                                    ; return (f x y)
                                    }
                                <|> return x


-----------------------------------------------------------
-- Tricky combinators
-----------------------------------------------------------
eof :: Parser ()
eof                 = notFollowedBy anySymbol <?> "end of input"

notFollowedBy :: Parser Char -> Parser ()
notFollowedBy p     = try (do{ c <- p; unexpected (show [c]) }
                           <|> return ()
                          )

manyTill :: Parser a -> Parser end -> Parser [a]
manyTill p end      = scan
                    where
                      scan  = do{ end; return [] }
                            <|>
                              do{ x <- p; xs <- scan; return (x:xs) }


lookAhead :: Parser a -> Parser a
lookAhead p         = do{ state <- getState
                        ; x <- p
                        ; setState state
                        ; return x
                        }

possible p = (fmap Just (try p)) <|> (return Nothing)

-----------------------------------------------------------
-- Parser state combinators
-----------------------------------------------------------
getPosition :: Parser SourcePos
getPosition         = do{ state <- getState; return (statePos state) }

getInput :: Parser Source
getInput            = do{ state <- getState; return (stateInput state) }


setPosition :: SourcePos -> Parser ()
setPosition pos     = do{ updateState (\(State input _) -> State input pos)
                        ; return ()
                        }

setInput :: Source -> Parser ()
setInput input      = do{ updateState (\(State _ pos)   -> State input pos)
                        ; return ()
                        }

getState            = updateState id
setState state      = updateState (const state)



-----------------------------------------------------------
-- Parser definition.
-----------------------------------------------------------
data Parser a       = Parser (State -> Consumed (Reply a))
runP (Parser p)     = p

data Consumed a     = Consumed a                --input is consumed
                    | Empty !a                  --no input is consumed

data Reply a        = Ok !a !State ParseError   --parsing succeeded with @a@
                    | Error ParseError          --parsing failed

data State          = State { stateInput :: !Source
                            , statePos   :: !SourcePos
                            }
type Source         = String

instance Show State where
  show (State s p) = "State "++(show s)++" "++(show p)

setExpectError msg err  = setErrorMessage (Expect msg) err
sysUnExpectError msg pos= Error (newErrorMessage (SysUnExpect msg) pos)
unknownError state      = newErrorUnknown (statePos state)

-----------------------------------------------------------
-- run a parser
-----------------------------------------------------------
parseFromFile :: Parser a -> SourceName -> IO (Either ParseError a)
parseFromFile p fname
    = do{ input <- readFile fname
        ; return (parse p fname input)
        }

parseFromHandle :: Parser a -> SourceName -> Handle -> IO (Either ParseError a)
parseFromHandle p fname h
    = do{ input <- hGetContents h
        ; return (parse p fname input)
        }

parse :: Parser a -> SourceName -> Source -> Either ParseError a
parse p name input
    = case parserReply (runP p (State input (initialPos name))) of
        Ok x _ _    -> Right x
        Error err   -> Left err

skip p (x @ (input,name,line,col,tabs)) =
   case parserReply (runP p (State input (SourcePos name line col tabs))) of
     Ok _ state _ -> state
     Error _ -> (State input (SourcePos name line col tabs))

parse2 p input
    = case parserReply (runP (whiteSpace >> p) (State input (initialPos "keyboard input"))) of
        Ok x (State cs _) _    -> Right(x,cs)
        Error err   -> Left(show err)

parserReply result
    = case result of
        Consumed reply -> reply
        Empty reply    -> reply


-----------------------------------------------------------
-- Functor: fmap
-----------------------------------------------------------
instance Functor Parser where
  fmap f (Parser p)
    = Parser (\state ->
        case (p state) of
          Consumed reply -> Consumed (mapReply reply)
          Empty    reply -> Empty    (mapReply reply)
      )
    where
      mapReply reply
        = case reply of
            Ok x state err -> let fx = f x
                              in seq fx (Ok fx state err)
            Error err      -> Error err


-----------------------------------------------------------
-- Monad: return, sequence (>>=) and fail
-----------------------------------------------------------
instance Monad Parser where
  return x
    = Parser (\state -> Empty (Ok x state (unknownError state)))

  (Parser p) >>= f
    = Parser (\state ->
        case (p state) of
          Consumed reply1
            -> Consumed $
               case (reply1) of
                 Ok x state1 err1 -> case runP (f x) state1 of
                                       Empty reply2    -> mergeErrorReply err1 reply2
                                       Consumed reply2 -> reply2
                 Error err1       -> Error err1

          Empty reply1
            -> case (reply1) of
                 Ok x state1 err1 -> case runP (f x) state1 of
                                       Empty reply2 -> Empty (mergeErrorReply err1 reply2)
                                       other        -> other
                 Error err1       -> Empty (Error err1)
      )


  fail msg
    = Parser (\state ->
        Empty (Error (newErrorMessage (Message msg) (statePos state))))


mergeErrorReply err1 reply
  = case reply of
      Ok x state err2 -> Ok x state (mergeError err1 err2)
      Error err2      -> Error (mergeError err1 err2)


-----------------------------------------------------------
-- MonadPlus: alternative (mplus) and mzero
-----------------------------------------------------------
pzero :: Parser a
pzero = mzero

instance MonadPlus Parser where
  mzero
    = Parser (\state -> Empty (Error (unknownError state)))

  mplus (Parser p1) (Parser p2)
    = Parser (\state ->
        case (p1 state) of
          Empty (Error err) -> case (p2 state) of
                                 Empty reply -> Empty (mergeErrorReply err reply)
                                 consumed    -> consumed
          other             -> other
      )

-----------------------------------------------------------
-- Primitive Parsers:
--  try, satisfy, onFail, unexpected and updateState
-----------------------------------------------------------
try :: Parser a -> Parser a
try (Parser p)
    = Parser (\state@(State input pos) ->
        case (p state) of
          Consumed (Error err)  -> Empty (Error (setErrorPos pos err))
          Consumed ok           -> Empty ok
          empty                 -> empty
      )

token p --obsolete, use "try" instead
    = try p

satisfy :: (Char -> Bool) -> Parser Char
satisfy test
    = Parser (\state@(State input (pos @ (SourcePos name line col tabs))) ->
        case input of
          (c:cs) | test c    -> let --newpos = updatePos pos c
                                    --newstate = State cs newpos -- these 2 lines replaced by next line
                                    newstate@(State _ newpos) = update c cs name line col tabs
                                in seq (forceState newstate) $
                                   Consumed (Ok c newstate (newErrorUnknown newpos))
                 | otherwise -> Empty (sysUnExpectError ("\""++(take 20 (c:cs))++"...\"\n            ^") pos)
          []     -> Empty (sysUnExpectError "" pos)
      )


forceState :: State -> State
forceState (st @ (State input (pos@(SourcePos name line column tabs)))) =
    seq line (seq column (seq tabs st))

----------------------------------------------------------------------
-- update is added to deal with inserting ";" and "{"
-- when layout information is used.
-- works in conjunction with the "layout" combinator in ParseToken.hs
----------------------------------------------------------------------

update c cs name line col tabs =
  case c of
    '\n'  -> skipToNextToken cs name (line+1) 1 tabs
    '\t'  -> State cs (SourcePos name line (col + 8 - ((col-1) `mod` 8)) tabs)
    '\r'  -> State cs (SourcePos name line col tabs)
    other -> State cs (SourcePos name line (col + 1) tabs)

xx = update '\n' " where tim = 3" "TE" 6 1 [1]
yy = skip whiteSpace (" where tim = 3","TE",6+1,1,[])


skipToNextToken input name line col [] = State input (SourcePos name line col [])
skipToNextToken input name line col (tabs@(p:ps)) =
   case skip whiteSpace (input,name,line,col,[]) of
     (State [] (SourcePos _ line2 col2 _)) -> -- No more input, close all the pending layout
          State (map (const '}') tabs) (SourcePos name line2 col2 [])
     (State cs (SourcePos _ line2 col2 _))
         | col2==p -> State (';':cs) (SourcePos name line2 (col2-1) tabs)
         | col2<p  -> adjust [] cs col2 tabs
         | col2>p  -> State cs (SourcePos name line2 col2 tabs)
      where adjust prefix cs column [] = State (rev prefix cs) (SourcePos name line2 column [])
            adjust prefix cs column (tabs @ (p:ps))
               | col2==p = State (rev (';':prefix) cs) (SourcePos name line2 (column-1) tabs)
               | col2<p  = --error ("STOP\n"++cs++(show tabs)++"\n"++(show col2)++prefix)
                           adjust ('}':prefix) cs (column - 1) ps
               | col2>p  = State (rev prefix cs) (SourcePos name line2 column tabs)
            rev [] ys = ys
            rev (x:xs) ys = rev xs (x:ys)


{-
skipToNextToken input name line col tabs =
 case (input,tabs) of
   (_,[]) -> State input (SourcePos name line col tabs)  -- No layout, do nothing
   ([],_) -> State input (SourcePos name line col tabs)  -- No input, do nothing
   (c:cs,p:ps) ->
      case c of
       '\n'  -> skipToNextToken cs name (line+1) 1 tabs
       '\t'  -> skipToNextToken cs name line (col + 8 - ((col-1) `mod` 8)) tabs
       ' '   -> skipToNextToken cs name line (col+1) tabs
       other | col==p -> State (';':input) (SourcePos name line (col-1) tabs)
             | col<p  -> adjust [] input col tabs
             | col>p  -> State input (SourcePos name line col tabs)
         where adjust prefix cs column [] = State cs (SourcePos name line column [])
               adjust prefix cs column (tabs @ (p:ps))
                 | col==p = State (rev (';':prefix) cs) (SourcePos name line (column-1) tabs)
                 | col<p  = adjust ('}':prefix) cs (column - 1) ps
                 | col>p  = State (rev prefix cs) (SourcePos name line column tabs)
               rev [] ys = ys
               rev (x:xs) ys = rev xs (x:ys)
-}

------------------------------------------------------------------------------


onFail :: Parser a -> String -> Parser a
onFail (Parser p) msg
    = Parser (\state ->
        case (p state) of
          Empty reply
            -> Empty $
               case (reply) of
                 Error err        -> Error (setExpectError msg err)
                 Ok x state1 err  | errorIsUnknown err -> reply
                                  | otherwise -> Ok x state1 (setExpectError msg err)
          other       -> other
      )


updateState :: (State -> State) -> Parser State
updateState f
    = Parser (\state -> Empty (Ok state (f state) (unknownError state)))


unexpected :: String -> Parser a
unexpected msg
    = Parser (\state -> Empty (Error (newErrorMessage
                                    (UnExpect (msg ++ " at: \""++(take 10 (stateInput state))++"...\""))
                                    (statePos state))))


-----------------------------------------------------------
-- Parsers unfolded for speed:
--  string
-----------------------------------------------------------

{- specification of @string@:
string s            = scan s
                    where
                      scan []     = return s
                      scan (c:cs) = do{ char c <?> show s; scan cs }
-}

one_at_a_time [] = return []
one_at_a_time (c:cs) =
    do { x <- satisfy (==c); xs <- one_at_a_time cs; return(x:xs) }

string :: String -> Parser String
string xs = if elem '\n' xs then one_at_a_time xs else stringHelp xs

stringHelp :: String -> Parser String
stringHelp s
    = Parser (\state@(State input pos) ->
       let
        ok cs             = let newpos   = updatePosString pos s
                                newstate = State cs newpos
                            in seq newpos $ seq newstate $
                               (Ok s newstate (newErrorUnknown newpos))

        errEof            = Error (setErrorMessage (Expect (show s))
                                     (newErrorMessage (SysUnExpect "") pos))
        errExpect c       = Error (setErrorMessage (Expect (show s))
                                     (newErrorMessage (SysUnExpect (show [c])) pos))

        walk [] cs        = ok cs
        walk xs []        = errEof
        walk (x:xs) (c:cs)| x == c        = walk xs cs
                          | otherwise     = errExpect c

        walk1 [] cs        = Empty (ok cs)
        walk1 xs []        = Empty (errEof)
        walk1 (x:xs) (c:cs)| x == c        = Consumed (walk xs cs)
                           | otherwise     = Empty (errExpect c)

       in walk1 s input)


-----------------------------------------------------------
-- White space & symbols
-- we moved the definitions for whiteSpce here, since
-- we'd get a set of mutually recursive modules if we don't.
-- we need white space in layout, since we need to skip to the next
-- non-whitespace character after a newline when in layout mode.
-- See the functions satisfy, and update above.
--
-- These versions use cEnd, cStart, cLine and nestedC from
-- the module CommentDef instead of the fields of TokenDef
-- Those fields now inherit the values in cEnd, cStart, cLine and nestedC
-----------------------------------------------------------

symbol name
    = lexeme (string name)

lexeme p
    = do{ x <- p; whiteSpace; return x  }


--whiteSpace
whiteSpace
    | noLine && noMulti  = skipMany (simpleSpace <?> "")
    | noLine             = skipMany (simpleSpace <|> multiLineComment <?> "")
    | noMulti            = skipMany (simpleSpace <|> oneLineComment <?> "")
    | otherwise          = skipMany (simpleSpace <|> oneLineComment <|> multiLineComment <?> "")
    where
      noLine  = null cLine  --(commentLine tokenDef)
      noMulti = null cStart --(commentStart tokenDef)


simpleSpace =
    skipMany1 (satisfy isSpace)

oneLineComment =
    do{ try (string cLine) --(commentLine tokenDef))
      ; skipMany (satisfy (/= '\n'))
      ; return ()
      }

multiLineComment =
    do { try (string cStart) --(commentStart tokenDef))
       ; inComment
       }

inComment
    | nestedC = inCommentMulti  --nestedComments tokenDef  = inCommentMulti
    | otherwise                = inCommentSingle

inCommentMulti
    =   do{ try (string cEnd) -- (commentEnd tokenDef))
          ; return () }
    <|> do{ multiLineComment                     ; inCommentMulti }
    <|> do{ skipMany1 (noneOf startEnd)          ; inCommentMulti }
    <|> do{ oneOf startEnd                       ; inCommentMulti }
    <?> "end of comment"
    where
      startEnd   = nub (cEnd ++ cStart) -- (commentEnd tokenDef ++ commentStart tokenDef)

inCommentSingle
    =   do{ try (string cEnd) --(commentEnd tokenDef))
          ; return () }
    <|> do{ skipMany1 (noneOf startEnd)         ; inCommentSingle }
    <|> do{ oneOf startEnd                      ; inCommentSingle }
    <?> "end of comment"
    where
      startEnd   = nub (cEnd ++ cStart) -- (commentEnd tokenDef ++ commentStart tokenDef)
