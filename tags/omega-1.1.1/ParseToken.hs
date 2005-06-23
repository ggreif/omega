-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Thu Jun 23 11:51:26 Pacific Daylight Time 2005
-- Omega Interpreter: version 1.1 (revision 1)

-----------------------------------------------------------
-- Daan Leijen (c) 1999, daan@cs.uu.nl
--
-- $version: 23 Feb 2000, release version 0.2$
-----------------------------------------------------------
module ParseToken( identifier, reserved, prefixIdentifier 
                 , oper,operator, reservedOp, isReservedName
                        
                 , charLiteral, stringLiteral 
                 , natural, integer, float, naturalOrFloat
                 , decimal, hexadecimal, octal           
             
                 , parens, braces, brackets, squares
                 , semi, comma, colon, dot
                 , semiSep, semiSep1 
                 , commaSep, commaSep1
                 , layout
                 ) where

import Char         (isSpace,digitToInt,isAlpha,toLower,toUpper)
import List         (nub,sort)
import Parser
import StdTokenDef  (TokenDef(..))
import TokenDef     (tokenDef)


-----------------------------------------------------------
-- Bracketing
-----------------------------------------------------------
parens p        = between (symbol "(") (symbol ")") p
braces p        = between (symbol "{") (symbol "}") p
brackets p      = between (symbol "<") (symbol ">") p
squares p       = between (symbol "[") (symbol "]") p

semi            = symbol ";" 
comma           = symbol ","
dot             = symbol "."
colon           = symbol ":"

commaSep p      = sepBy p comma
semiSep p       = sepBy p semi

commaSep1 p     = sepBy1 p comma
semiSep1 p      = sepBy1 p semi


-----------------------------------------------------------
-- Chars & Strings
-----------------------------------------------------------
charLiteral :: Parser Char
charLiteral     = lexeme (between (char '\'') 
                                  (char '\'' <?> "end of character")
                                  characterChar )
                <?> "character"

characterChar   = charLetter <|> charEscape 
                <?> "literal character"

charEscape      = do{ char '\\'; escapeCode }
charLetter      = satisfy (\c -> (c /= '\'') && (c /= '\\') && (c > '\026'))



stringLiteral :: Parser String
stringLiteral   = lexeme (
                  do{ str <- between (char '"')                   
                                     (char '"' <?> "end of string")
                                     (many stringChar) 
                    ; return (foldr (maybe id (:)) "" str)
                    }
                  <?> "literal string")

stringChar :: Parser (Maybe Char)
stringChar      =   do{ c <- stringLetter; return (Just c) }
                <|> stringEscape 
                <?> "string character"
            
stringLetter    = satisfy (\c -> (c /= '"') && (c /= '\\') && (c > '\026'))

stringEscape    = do{ char '\\'
                    ;     do{ escapeGap  ; return Nothing }
                      <|> do{ escapeEmpty; return Nothing }
                      <|> do{ esc <- escapeCode; return (Just esc) }
                    }
                    
escapeEmpty     = char '&'
escapeGap       = do{ many1 space
                    ; char '\\' <?> "end of string gap"
                    }
                    
                    
                    
-- escape codes
escapeCode      = charEsc <|> charNum <|> charAscii <|> charControl
                <?> "escape code"

charControl :: Parser Char
charControl     = do{ char '^'
                    ; code <- upper
                    ; return (toEnum (fromEnum code - fromEnum 'A'))
                    }

charNum :: Parser Char                    
charNum         = do{ code <- decimal 
                              <|> do{ char 'o'; number 8 octDigit }
                              <|> do{ char 'x'; number 16 hexDigit }
                    ; return (toEnum (fromInteger code))
                    }

charEsc         = choice (map parseEsc escMap)
                where
                  parseEsc (c,code)     = do{ char c; return code }
                  
charAscii       = choice (map parseAscii asciiMap)
                where
                  parseAscii (asc,code) = try (do{ string asc; return code })


-- escape code tables
escMap          = zip ("abfnrtv\\\"\'") ("\a\b\f\n\r\t\v\\\"\'")
asciiMap        = zip (ascii3codes ++ ascii2codes) (ascii3 ++ ascii2) 

ascii2codes     = ["BS","HT","LF","VT","FF","CR","SO","SI","EM",
                   "FS","GS","RS","US","SP"]
ascii3codes     = ["NUL","SOH","STX","ETX","EOT","ENQ","ACK","BEL",
                   "DLE","DC1","DC2","DC3","DC4","NAK","SYN","ETB",
                   "CAN","SUB","ESC","DEL"]

ascii2          = ['\BS','\HT','\LF','\VT','\FF','\CR','\SO','\SI',
                   '\EM','\FS','\GS','\RS','\US','\SP']
ascii3          = ['\NUL','\SOH','\STX','\ETX','\EOT','\ENQ','\ACK',
                   '\BEL','\DLE','\DC1','\DC2','\DC3','\DC4','\NAK',
                   '\SYN','\ETB','\CAN','\SUB','\ESC','\DEL']


-----------------------------------------------------------
-- Numbers
-----------------------------------------------------------
naturalOrFloat :: Parser (Either Integer Double)
naturalOrFloat  = lexeme (natFloat) <?> "number"

float           = lexeme floating   <?> "float"
integer         = lexeme int        <?> "integer"
natural         = lexeme nat        <?> "natural"


-- floats
floating        = do{ n <- decimal 
                    ; fractExponent n
                    }


natFloat        =  try decimalFloat 
               <|> do{ char '0'
                     ; zeroNumFloat
                     }
                  
                  
zeroNumFloat    = do{ n <- hexadecimal <|> octal
                    ; return (Left n)
                    }
                <|> decimalFloat 
                <|> return (Left 0)                  
                  
decimalFloat    = do{ n <- decimal 
                    ; option (Left n) 
                             (do{ f <- fractExponent n; return (Right f)})
                    }

                    
fractExponent n = do{ fract <- fraction
                    ; expo  <- option 1.0 exponent'
                    ; return ((fromInteger n + fract)*expo)
                    }
                <|>
                  do{ expo <- exponent'
                    ; return ((fromInteger n)*expo)
                    }

fraction        = do{ char '.'
                    ; digits <- many1 digit <?> "fraction"
                    ; return (foldr op 0.0 digits)
                    }
                  <?> "fraction"
                where
                  op d f    = (f + fromIntegral (digitToInt d))/10.0
                    
exponent'       = do{ oneOf "eE"
                    ; f <- sign
                    ; e <- decimal <?> "exponent"
                    ; return (power (f e))
                    }
                  <?> "exponent"
                where
                   power e  | e < 0      = 1.0/power(-e)
                            | otherwise  = fromInteger (10^e)


-- integers and naturals
int             = do{ f <- lexeme sign
                    ; n <- nat
                    ; return (f n)
                    }
                    
sign            :: Parser (Integer -> Integer)
sign            =   (char '-' >> return negate) 
                <|> (char '+' >> return id)     
                <|> return id

nat             = zeroNumber <|> decimal
    
zeroNumber      = do{ char '0'
                    ; hexadecimal <|> octal <|> decimal <|> return 0
                    }
                  <?> ""       

decimal         = number 10 digit        
hexadecimal     = do{ oneOf "xX"; number 16 hexDigit }
octal           = do{ oneOf "oO"; number 8 octDigit  }

number :: Integer -> Parser Char -> Parser Integer
number base baseDigit
    = do{ digits <- many1 baseDigit
        ; let n = foldl (\x d -> base*x + toInteger (digitToInt d)) 0 digits
        ; seq n (return n)
        }          

-----------------------------------------------------------
-- Operators & reserved ops
-----------------------------------------------------------
reservedOp name =   
    lexeme $ try $
    do{ string name
      ; notFollowedBy (opLetter tokenDef) <?> ("end of " ++ show name)
      }

operator =
    lexeme $ try $
    do{ name <- oper
      ; if (isReservedOp name)
         then unexpected ("reserved operator " ++ show name)
         else return name
      }
      
oper =
    do{ c <- (opStart tokenDef)
      ; cs <- many (opLetter tokenDef)
      ; return (c:cs)
      }
    <?> "operator"
    
isReservedOp name =
    isReserved (sort (reservedOpNames tokenDef)) name          
    
    
-----------------------------------------------------------
-- Identifiers & Reserved words
-----------------------------------------------------------
reserved name =
    lexeme $ try $
    do{ caseString name
      ; notFollowedBy (identLetter tokenDef) <?> ("end of " ++ show name)
      }

caseString name
    | caseSensitive tokenDef  = string name
    | otherwise               = do{ walk name; return name }
    where
      walk []     = return ()
      walk (c:cs) = do{ caseChar c <?> msg; walk cs }
      
      caseChar c  | isAlpha c  = char (toLower c) <|> char (toUpper c)
                  | otherwise  = char c
      
      msg         = show name
      

identifier =
    lexeme $ try $
    do{ name <- ident
      ; if (isReservedName name)
         then unexpected ("reserved word " ++ show name)
         else return name
      }

prefixIdentifier c =
    lexeme $ try $
    do{ char c
      ; name <- ident
      ; if (isReservedName name)
         then unexpected ("reserved word " ++ show name)
         else return name
      }

    
ident           
    = do{ c <- identStart tokenDef
        ; cs <- many (identLetter tokenDef)
        ; return (c:cs)
        }
    <?> "identifier"

isReservedName name
    = isReserved theReservedNames caseName
    where
      caseName      | caseSensitive tokenDef  = name
                    | otherwise               = map toLower name

    
isReserved names name    
    = scan names
    where
      scan []       = False
      scan (r:rs)   = case (compare r name) of
                        LT  -> scan rs
                        EQ  -> True
                        GT  -> False

theReservedNames
    | caseSensitive tokenDef  = sortedNames
    | otherwise               = map (map toLower) sortedNames
    where
      sortedNames   = sort (reservedNames tokenDef)
                             

--------------------------------------------
-- Haskell style combinators

layoutSep   = (symbol ";") <?> "inserted layout separator (;)"
layoutEnd   = (symbol "}") <?> "inserted layout closing brace"
layoutBegin = (symbol "{") <?> "layout opening brace"

indent =
  do { (SourcePos cs line col tabs) <- getPosition
     ; setPosition (SourcePos cs line col (col : tabs))
     }
undent =
  do { (SourcePos cs line col (p:ps)) <- getPosition
     ; setPosition (SourcePos cs line col ps)
     }     

align :: Parser a -> Parser b -> Parser [a]
align p stop =
  do { x <- p
     ; whiteSpace
     ; (do { try layoutSep; xs <- align p stop; return (x:xs)}) <|>
       (do { try layoutEnd; stop; return[x]}) <|> 
           -- removing indentation happens automatically 
           -- in function "update", if we see layoutEnd
       (do { stop; undent; return [x]})                                            
     }
            
layout :: Parser a -> Parser b -> Parser [a]     
layout p stop = 
  (do { try layoutBegin; xs <- semiSep p
      ; layoutEnd <?> "explicit layout closing brace"
      ; stop; return xs}) <|>
  (do { indent; xs <- align p stop; return xs})
        
w = skip whiteSpace ("\n --hdfhdf\n   56 is ok","SKIP",1,1,[])
