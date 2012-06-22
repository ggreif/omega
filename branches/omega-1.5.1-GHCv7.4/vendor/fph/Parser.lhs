Parser for the little language of the paper

  exp ::= integer
	| var
	| exp1 exp2
	| let var = exp1 in exp2
	| exp :: sig
	| ( exp )

  sig = rho | forall tv1 .. tvn . rho
  rho = tv  | Int | Bool | sig -> rho

\begin{code}
module Parser where

import BasicTypes

import List ( nub ) 

import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language( haskellDef )

langDef :: P.LanguageDef st
langDef = haskellDef { P.reservedNames = ["let", "in", "forall","data","case","of", "where" ],
                       P.reservedOpNames = ["::", "\\", ".", "->", "|"] }

lexer      :: P.TokenParser st
lexer       = P.makeTokenParser langDef
    
parens     :: CharParser st a -> CharParser st a
parens      = P.parens lexer
integer    :: CharParser st Integer
integer     = P.integer lexer
reservedOp :: String -> CharParser st ()
reservedOp  = P.reservedOp lexer
reserved   :: String -> CharParser st ()
reserved    = P.reserved lexer
identifier :: CharParser st String
identifier  = P.identifier lexer 

constructor :: CharParser st String 
constructor  = 
  do { h <- upper 
     ; t <- many alphaNum
     ; whiteSpace 
     ; return (h:t) } 

dot        :: CharParser st String
dot	        = P.dot lexer
whiteSpace :: CharParser st ()
whiteSpace  = P.whiteSpace lexer
lexeme     :: CharParser st ()
lexeme      = P.whiteSpace lexer

parserToReadS :: Parser a -> ReadS a
parserToReadS p s = case parse (whiteSpace >> p) "" s of
			Left _err -> []
			Right a  -> [(a,"")]

-- -- Patterns 
-- instance Read Pattern where
--   readsPrec _ = parserToReadS readPat

readPat :: Parser Pattern 
readPat = choice [try annpat, try conpat, atomPat Nothing]

atomPat :: Maybe Column -> Parser Pattern
atomPat Nothing = choice [try varpat, try defpat, parens readPat]
atomPat (Just cp) 
  = do { whiteSpace
       ; pos <- getPosition 
       ; if (cp < sourceColumn pos) then 
             choice [try varpat, try defpat, parens readPat]
         else pzero } 

varpat :: Parser Pattern
varpat = do { v <- identifier; return (PVar v) }

defpat :: Parser Pattern
defpat = do { reservedOp "_"; return (PAny) }

annpat :: Parser Pattern
annpat = do { p <- atomPat Nothing
	     ; reservedOp "::" 
	     ; ty <- readSigma 
	     ; return (PAnn p ty) }

conpat :: Parser Pattern
conpat = do { whiteSpace 
            ; p <- getPosition  
            ; cn <- constructor 
            ; pts <- many (atomPat (Just (sourceColumn p))) 
            ; return (PCon cn pts) }

-- Declarations 

parseDecls :: Parser [Decl]
parseDecls 
  = do { whiteSpace
       ; ds <- many readDecl
       ; eof
       ; return ds }

readDecl :: Parser Decl
readDecl = choice [dataDecl, try anndefDecl, defDecl ]

dataDecl :: Parser Decl 
dataDecl = do { reserved "data";
              ; n <- constructor; 
              ; vars <- readTvs 
              ; reserved "where"
              ; whiteSpace 
              ; cs <- many (conDecl vars)
              ; return (Data n vars cs) } 
  where conDecl :: [Name] -> Parser Ctor
        conDecl vars = do { cn <- constructor 
                          ; reservedOp "::" 
                          ; ty <- readSigma 
                          ; case vars of 
                              [] ->
                                  return (Ctor cn ty) 
                              _  -> case ty of 
                                      ForAll vars' ty' -> 
                                        return  $ Ctor cn (ForAll (nub $ (map BoundTv vars)++vars') ty')
                                      _ -> return $ Ctor cn (ForAll (map BoundTv vars) ty)
                          }

defDecl :: Parser Decl
defDecl = do { f <- identifier 
             ; xs <- many readPat
             ; reservedOp "=" 
             ; rhs <- readTerm 
             ; return (Def f xs rhs) }

anndefDecl :: Parser Decl 
anndefDecl = do { f <- identifier 
                ; reservedOp "::" 
                ; ty <- readSigma 
                ; return (AnnDef f ty) }

-- instance Read Term where
--   readsPrec _ = parserToReadS readTerm

-- instance Read Type where
--   readsPrec _ = parserToReadS readSigma


readTerm :: Parser Term
readTerm = choice [try ann, non_ann]

non_ann :: Parser Term
non_ann = choice [lam, try rlet, rannlet, rcase, app]

atom :: Maybe Column -> Parser Term
atom Nothing   = choice [parens readTerm, lit, var]
atom (Just hp) = do { whiteSpace 
                    ; pos <- getPosition
                    ; if (hp < sourceColumn pos) then 
                            choice [parens readTerm, lit, var]
                          else pzero }

lit :: Parser Term
lit = do { i <- integer; return (Lit (fromInteger i)) }

var :: Parser Term
var = do { v <- identifier; return (Var v) }


app :: Parser Term
app = do { whiteSpace
         ; pos <- getPosition
         ; fun <- atom Nothing
         ; args <- many (atom (Just (sourceColumn pos))) 
	 ; return (foldl App fun args) }

lam :: Parser Term
lam = do { reservedOp "\\"
         ; p <- readPat 
	  ; reservedOp "->" 
	  ; body <- readTerm 
	  ; return (Lam p body) }

rlet :: Parser Term
rlet = do { reserved "let" 
          ; v <- identifier
          ; reservedOp "=" 
          ; rhs <- readTerm
   	   ; reserved "in"
	   ; body <- readTerm 
	   ; return (Let v rhs body) }

rannlet :: Parser Term
rannlet = do { reserved "let" 
             ; v <- identifier
             ; reservedOp "::"
             ; ty <- readSigma
             ; v' <- identifier 
             ; reservedOp "=" 
             ; rhs <- readTerm
   	     ; reserved "in"
	     ; body <- readTerm 
             ; if (v == v') then return (AnnLet v ty rhs body) 
               else pzero }

ralt :: Column -> Parser (Pattern,Term) 
ralt cp = do { whiteSpace
             ; pos <- getPosition 
             ; if (cp < sourceColumn pos) then 
                 do { p <- readPat
                    ; reservedOp "->" 
                    ; rhs <- readTerm
                    ; return (p,rhs) }
               else pzero } 

rcase :: Parser Term
rcase = do { whiteSpace
           ; pos <- getPosition 
           ; reserved "case" 
 	    ; scrut <- readTerm
	    ; reserved "of"
           ; alts <- many (ralt (sourceColumn pos)) 
	    ; return (Case scrut alts) }

ann :: Parser Term
ann = do { term <- non_ann
	  ; reservedOp "::"
	  ; ty <- readSigma 
	  ; return (Ann term ty) }

---------------------------------
--	Types
---------------------------------

readSigma :: Parser Sigma	-- Not necessarily with parens
readSigma = choice [try readRho, try (parens readSigma), sigma ]

atomSigma :: Maybe Column -> Parser Sigma
atomSigma Nothing = choice [try (parens sigma), atomRho Nothing]
atomSigma (Just cp) = do { whiteSpace; 
                         ; pos <- getPosition 
                         ; if (cp < sourceColumn pos) then 
                               choice [try (parens sigma), atomRho Nothing]
                           else pzero } 
sigma :: Parser Sigma
sigma = do { reserved "forall" 
	    ; tvs <- readTvs 
	    ; dot
	    ; tau <- readRho
	    ; return (ForAll (nub $ map BoundTv tvs) tau) }

readRho :: Parser Rho	-- Not necessarily with parens
readRho = choice [try rfun, try tcon, atomRho Nothing]

rfun :: Parser Rho
rfun = do { arg <- choice [try tcon, atomSigma Nothing]
          ; reservedOp "->"
 	   ; res <- readSigma; return (Fun arg res) }

atomRho :: Maybe Column -> Parser Rho
atomRho Nothing = choice [try unaryCons, try tvar, (parens readRho)]
atomRho (Just cp) = do { whiteSpace
                        ; pos <- getPosition 
                        ; if (cp < sourceColumn pos) then 
                              choice [try unaryCons, try tvar, parens readRho]
                          else pzero }
tcon :: Parser Rho
tcon = do { whiteSpace
          ; pos <- getPosition 
          ; n <- constructor
          ; args <- many (atomSigma (Just (sourceColumn pos))) 
          ; return (TyCon n args) } 

tvar :: Parser Tau
tvar = do { v <- identifier
	  ; return (TyVar (BoundTv v)) }

unaryCons :: Parser Type 
unaryCons = try $ do { c <- constructor; return (TyCon c []) }

--------------
readTvs :: Parser [Name]
readTvs = many identifier

\end{code}
