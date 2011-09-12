Parser for the little language of the paper

  exp ::= integer
        | var
        | exp1 exp2
        | let var = exp1 in exp2
        | exp :: sig
        | ( exp )
        | \ var . exp
        | \ ( var :: sig ) . exp

  sig = forall tv1 .. tvn . rho
  rho = tv  | Int | Bool | sig -> sig

\begin{code}
module Parser where

import BasicTypes hiding( dot )

import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language( haskellDef )

langDef :: P.LanguageDef st
langDef = haskellDef { P.reservedNames = ["let", "in", "forall"]
                     , P.reservedOpNames = ["::", "\\", ".", "->"] }

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
dot        :: CharParser st String
dot         = P.dot lexer
whiteSpace :: CharParser st ()
whiteSpace  = P.whiteSpace lexer
lexeme     :: CharParser st ()
lexeme      = P.whiteSpace lexer

parserToReadS :: Parser a -> ReadS a
parserToReadS p s = case parse (whiteSpace >> p) "" s of
                        Left _err -> []
                        Right a  -> [(a,"")]


-----------------------------
instance Read Term where
  readsPrec _ = parserToReadS readTerm

instance Read Sigma where
  readsPrec _ = parserToReadS readSigma

-----------------------------
parseTerm :: Parser Term
parseTerm = do { whiteSpace
               ; t <- readTerm
               ; eof
               ; return t }

readTerm :: Parser Term
readTerm = try ann <|> non_ann

non_ann :: Parser Term
non_ann = lam <|> rlet <|> app

atom :: Parser Term
atom = parens readTerm <|> lit <|> var

lit :: Parser Term
lit = do { i <- integer; return (Lit (fromInteger i)) }

var :: Parser Term
var = do { v <- identifier; return (Var v) }


app :: Parser Term
app = do { (fun:args) <- many1 atom
         ; return (foldl App fun args) }

lam :: Parser Term
lam = do { reservedOp "\\" ;
           ann_lam <|> ord_lam }

ord_lam :: Parser Term
ord_lam = do { v <- identifier
             ; dot
             ; body <- readTerm
             ; return (Lam v body) }

ann_lam :: Parser Term
ann_lam = do { (v,ty) <- parens (do {
                            v <- identifier ;
                            reservedOp "::" ;
                            ty <- readSigma ;
                            return (v, ty) })
             ; dot
             ; body <- readTerm
             ; return (ALam v ty body) }

rlet :: Parser Term
rlet = do { reserved "let"
          ; v <- identifier
          ; reservedOp "="
          ; rhs <- readTerm
          ; reserved "in"
          ; body <- readTerm
          ; return (Let v rhs body) }

ann :: Parser Term
ann = do { term <- non_ann
         ; reservedOp "::"
         ; ty <- readSigma
         ; return (Ann term ty) }

---------------------------------
--        Types
---------------------------------
exRho2Sigma :: [TyVar] -> ExRho -> Sigma
exRho2Sigma bs (Ex r) = ForAll bs r


readSigma :: Parser Sigma        -- Not necessarily with parens
readSigma =     try (parens readSigma)
            <|> sigma
            <|> fmap (exRho2Sigma []) readRho

atomSigma :: Parser Sigma
atomSigma =     try (parens sigma)
            <|> fmap (exRho2Sigma []) atomRho

sigma :: Parser Sigma
sigma = do { reserved "forall"
           ; tvs <- readTvs
           ; dot
           ; rho <- readRho
           ; return $ exRho2Sigma (map BoundTv tvs) rho }

--------------
readRho :: Parser ExRho          -- Not necessarily with parens
readRho = try rfun <|> atomRho

rfun :: Parser ExRho
rfun = do { arg <- atomSigma
          ; reservedOp "->"
          ; res <- atomSigma
          ; return $ Ex (Fun arg res) }

atomRho :: Parser ExRho
atomRho = try (fmap Ex tvar) <|> (fmap Ex tcon) <|> parens readRho

--------------
readTau :: Parser Tau            -- Not necessarily with parens
readTau = try tfun <|> atomTau

atomTau :: Parser Tau
atomTau = try tvar <|> tcon <|> parens readTau

tvar, tfun, tcon :: Parser Tau
tvar = do { v <- identifier;
            if (v == "Int" || v == "Bool")
             then fail "" else return ();
            return (TyVar (BoundTv v)) }
tfun = do { arg <- atomTau
          ; reservedOp "->"
          ; res <- readTau
          ; return (Fun arg res) }
tcon =     try $ do { "Int"  <- identifier; return intType }
       <|> do { "Bool" <- identifier; return boolType }

--------------
readTvs :: Parser [Name]
readTvs = many identifier
\end{code}
