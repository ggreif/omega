-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Thu Jun 23 11:51:26 Pacific Daylight Time 2005
-- Omega Interpreter: version 1.1 (revision 1)

module ParserDef (pp,pe,pd,name,getExp,getInt,
                pattern,expr,decl,
                bind,program,parse2,parse,parseString,parseFile
                ,Command(..),pCommand 
                ,d1)
                where

-- To import ParserAll you must define CommentDef.hs and TokenDef.hs
-- These should be in the same directory as this file.

import ParserAll
import Syntax(Exp(..),Pat(..),Body(..),Lit(..),Inj(..),Program(..)
             ,Dec(..),Constr(..),Stmt(..),Var(..)
             ,listExp,patTuple,ifExp,mergeFun,consExp,expTuple
             ,binop,opList,var,freshE,swp,dvars,evars,
             typeStrata,kindStrata,emptyF,Vars(..),freeOfDec
             ,ExplicitGADT(..),transGADT,okGADT
             ,freshNames,step1,step2,step3,step4,monadDec)
import Monads
import RankN(PT(..),typN,simpletyp,proposition,pt,allTyp
            ,ptsub,getFree,parse_tag,buildNat,props)
import Auxillary(Loc(..),plistf,plist)

---------------------------------------------------------

loc p = SrcLoc (sourceLine p) (sourceColumn p)

-------------------------------------------------------------


go s = parse expr "" s
g s = parse pattern "" s
f p s = parse p "" s
pp = parse2 pattern
pe = parse2 expr
pd = parse2 decl
pa = parse2 arm

getInt :: Monad m => (String -> m Int) -> String -> m Int
getInt failf s = case parse2 natural s of
              Left s -> failf s
              Right(n,s) -> return(fromInteger n)

getExp :: Monad m => String -> m Exp
getExp s = case pe s of
             Left s -> fail s
             Right(exp,rest) -> return exp

test1 =
  do { Right (Program p) <- pprog "work.prg"
     ; putStrLn(plistf f "\n*******" p "\n" "\n******")
     }
 where f x = show x++"\n"++show(freeOfDec x)   
     

bind :: Parser (Either (Pat,Exp) Exp) -- useful inside the Command loop
bind = (try (do { x <- pattern; symbol "<-"; e <- expr; return(Left(x,e))})) <|>
       (fmap Right expr)
pb = parse2 bind

pprog x = parseFromFile program x

{-
test =
  do { s <- readFile "test.hs"
     ; case parse2 vdecl s of
         Left message -> putStrLn message
         Right(d,_)   -> putStrLn(show d)
     }

testd = ppTC(parseFile program "test.hs")
-}


------------------------------------------------------------------

parseString :: Monad a => Parser b -> [Char] -> a (Either [Char] (b,[Char]))
parseString p s = (case parse2 p s of
                    Right(x,s) -> return(Right(x,s))
                    Left s -> return(Left s))

parseFile p s = comp
  where comp =  do { x <- parseFromFile p s
                   ; case x of
                       Left err -> return(Left(show err))
                       Right y -> return(Right y)
                   }



------------------------------------------------------------
-- The literals we parse are not quite the literals of the language
-- So make a temporary type used only in this file.

data Literal 
  = LInt Int 
  | LChar Char 
  | LString String 
  | LChrSeq String
  | LTag String
  | LFloat Double
  | LNat Int

-- Map the temporary type to the Exp type.
lit2Exp (LInt n) = Lit(Int n)
lit2Exp (LChar c) = Lit(Char c)
lit2Exp (LString s) = listExp (map (Lit . Char) s)
lit2Exp (LChrSeq s) = Lit(ChrSeq s)
lit2Exp (LFloat n) = Lit(Float (doubleToFloat n))
lit2Exp (LTag n) = Lit(Tag n)
lit2Exp (LNat n) = buildNat (Var(Global "Z")) sExp n

doubleToFloat :: Double -> Float
doubleToFloat n = encodeFloat a b
  where (a,b) = decodeFloat n
-----------------------------------------------------------
-- Terminals of the grammar. I.e. Literals variables and constructors
-----------------------------------------------------------

literal :: (Literal -> a) -> Parser a
literal fromLit =
    do{ v <- try hashLiteral <|> numLiteral <|> 
             chrLiteral <|> strLiteral <|> atomLiteral
      ; return $ fromLit v
      }
    <?> "literal"
  
--floatLiteral = do { m <- float; return(LFloat m)}

chrLiteral  = do{ c <- charLiteral; return (LChar c) }
strLiteral  = do{ s <- stringLiteral; return(LString s) }
hashLiteral = do { char '#'; 
                   ; (do {s <- stringLiteral; return(LChrSeq s)}) <|>
                     (do {n <- natural; return(LNat (fromInteger n))})}
numLiteral = do { n <- naturalOrFloat
                ; case n of
                    Left i -> return (LInt (fromInteger i))
                    Right r -> return(LFloat r)
                }
atomLiteral = parse_tag LTag
       
constructorName = lexeme (try construct)
  where construct = do{ c <- upper
                      ; cs <- many (identLetter tokenDef)
                      ; return (Global (c:cs))
                      }
                    <?> "Constructor name"
                                 

testSym = lexeme (string "##test")

terminal p inject = do { v <- p; return (inject v)}

expvariable,expconstructor :: Parser Exp
expvariable = terminal identifier (Var . Global)
expconstructor = terminal constructorName (\ s -> Var s)

patvariable :: Parser Pat
patvariable = terminal identifier (Pvar . Global)

name,constructor :: Parser Var
constructor = terminal constructorName id
name = terminal identifier Global

-----------------------------------------------------------
-------------------------------------------------------------
-- Pattern parsing

pattern =
      try asPattern
  <|> try (do { p <- simplePattern; symbol "::"; t <- typN 0; return(Pann p t)})
  <|> try infixPattern  -- There's a problem with infix
                        -- E.g. (L x : xs) parses as (L(x:xs)) rather than ((L x) : xs)
                        -- This will need to be fixed
  <|> conApp
  <|> simplePattern
  <?> "pattern"

asPattern =
  do { x <- name
     ; symbol "@"
     ; p <- pattern
     ; return (Paspat x p)
     }

infixPattern =
  do { p1 <- simplePattern
     ; x <- constrOper
     ; p2 <- pattern
     ; return (Pcon (Global x) [p1,p2])
     }
simplePattern :: Parser Pat
simplePattern =
        literal lit2Pat
    <|> try natPat
    <|> try(around pPat aroundInfo)
    -- <|> try(parensORtuple pattern patTuple)
    -- <|> listExpression pattern pConsUp
    <|> (do { symbol "_"; return Pwild})
    <|> (do { nm <- constructor; return(Pcon nm []) })
    <|> patvariable
    <?> "simple pattern"

conApp =
   do { name <- constructor
      ; ps <- many simplePattern
      ; return (pcon name ps)
      }

pcon (Global "L") [p] = Psum L p
pcon (Global "R") [p] = Psum R p
pcon (Global "Ex") [p] = Pexists p
pcon n ps = Pcon n ps

constrOper = lexeme $ try $
    (do{ c <- char ':'
       ; cs <- many (opLetter tokenDef)
       ; return (c:cs)
       }
     <?> "infix constructor operator")

lit2Pat (LInt n) = Plit(Int n)
lit2Pat (LChar c) = Plit(Char c)
lit2Pat (LChrSeq s) = Plit(ChrSeq s)
lit2Pat (LFloat n) = Plit(Float(doubleToFloat n))
lit2Pat (LTag x) = Plit(Tag x)
lit2Pat (LString s) = pConsUp (map (Plit . Char) s)
lit2Pat (LNat n) = buildNat (Pcon (Global "Z")[]) s n
  where s x = Pcon (Global "S") [x]

-----------------------------------------------------------------------
-- Parsing Lists and Tuples of any size. E.g. [1,2,3] (3,4,5)

listExpression p fromListP =
  do { xs <- bracketList (symbol "[") (symbol "]") (symbol ",") p
     ; return (fromListP xs)
     }

parensORtuple p fromListP =
  do { xs <- bracketList (symbol "(") (symbol ")") (symbol ",") p
     ; return (fromListP xs)
     }

bracketList open close sep p =
  do{ open; x <- sepBy p sep; close; return x }

----------------------------------------------------------
-- Parsers for things that are bracketed. We make it table
-- driven so that it is easy to add new syntactic sugar.


aroundInfo :: Monad m => [(Parser String, Parser String,Parser String,[Exp] -> m Exp,[Pat] -> m Pat)]
aroundInfo = 
  [( symbol "(",  symbol ")",  symbol ","
     , return . expTuple, return . patTuple)
  ,( try (symbol "["),  symbol "]",  symbol ","
     , return . listExp,  return . pConsUp)
  ,( resOp "[|", resOp "|]", symbol ","
     , codeExp, codePat)
  ,( try(resOp "#["), symbol "]", symbol ","
   , return . (foldr cAdd cEmpty),return . vecUp )
  ,( try(resOp "#("), symbol ")", symbol ","
   , prodTuple,patTuple2 )
  ]

zw = parse2 (around pExp aroundInfo) "(Decl `inpz )"
zw2 = parse2 ( sepBy expr (symbol ",") ) 
             "Decl `inpz )"
q = "(Decl `inpz )"


resOp x = reservedOp x >> return ""

around pf [x] = pf x
around pf (x:xs) = pf x <|> around pf xs

pExp (open,close,sep,expf,patf) = 
     do { open; xs <- sepBy expr sep; close; expf xs}
       
pPat (open,close,sep,expf,patf) = 
     do { open; xs <- sepBy pattern sep; close; patf xs}


cAdd x y = (App (App (Var (Global "CAdd")) x) y)
cEmpty = (Var (Global "CEmpty"))

vecUp [] = Pcon (Global "CEmpty") []
vecUp (p:ps) = Pcon (Global "CAdd") [p,vecUp ps]

codeExp [] = fail "Code brackets cannot be empty."
codeExp [x] = return(Bracket x)
codeExp xs = fail ("Code brackets surround only one expression.\n  "++
                   plist "[|" xs "," "|]")             
codePat ps = fail ("Code brackets cannot appear in patterns.\n  "++
                   plist "[|" ps "," "|]")         

pConsUp [] = Pcon (Global "[]") []
pConsUp (p:ps) = Pcon (Global ":") [p,pConsUp ps]

prodTuple [] = fail "No empty tuples: #()"
prodTuple [p] = return (n_plus_x p)
prodTuple [x,y] = return (prodPair x y)
prodTuple (x:xs) = do { y <- prodTuple xs; return(prodPair x y)}

prodPair x y = (App (App (Var (Global "Pair")) x) y)

patTuple2 [] = fail "No empty tuples: #()"
patTuple2 [p] = return p
patTuple2 [x,y] = return (prodp x y)
patTuple2 (x:xs) = do { y <- patTuple2 xs; return(prodp x y)}

prodp x y = Pcon (Global "Pair") [x,y]

------------------------------------------------------
-- Parsers for syntactic sugar for Natural numbers

natLiteral :: (Var -> a) -> a -> (a -> a) -> Parser a
natLiteral var z s = do{ symbol "#"; nplus }
  where -- npat = do { n <- natural; return(buildNat z s n)}
        -- This form handled in literals. See hashLiteral
        nplus = parens(plus name natural f <|> plus natural name g)
        plus p q f = do { x <- try p; symbol "+"; n <- q; f x n}
        f name n = return(buildNat (var name) s n)
        g n name = return(buildNat (var name) s n)
         
natExp :: Parser Exp
natExp = natLiteral Var z sExp
  where z = (Var(Global "Z"))
        
sExp x = App (Var (Global "S")) x

natPat :: Parser Pat
natPat = natLiteral Pvar z s 
  where z = Pcon (Global "Z") []
        s x = Pcon (Global "S") [x]

n_plus_x (App (App (Var (Global "+"))
                   (Lit (Int n)))
              (x@(Var (Global name)))) = buildNat x sExp n
n_plus_x (App (App (Var (Global "+"))
                   (x@(Var (Global name))))
               (Lit (Int n))) = buildNat x sExp n  
n_plus_x term = term   
   
-----------------------------------------------------------
-- Expressions
-----------------------------------------------------------

expr :: Parser Exp
expr =
        lambdaExpression
    <|> letExpression
    <|> circExpression
    <|> ifExpression
    <|> doexpr
    <|> checkExp
    <|> lazyExp
    <|> existExp
    <|> underExp
    <|> try (do { p <- simpleExpression; symbol "::"
                ; t <- typN 0
                ; return(Ann p t)})
    <|> try runExp
    <|> infixExpression     --names last
    <?> "expression"

checkExp =
    do { reserved "check"
       ; e <- expr
       ; return(CheckT e)
       }
       
lazyExp =
    do { reserved "lazy"
       ; e <- expr
       ; return(Lazy e)
       }

runExp  =
    do { reserved "run"
       ; e <- expr
       ; return (Run e) }

existExp =
    do { reserved "Ex"
       ; e <- expr
       ; return(Exists e)
       }

underExp =
    do { reserved "under"
       ; e1 <- simpleExpression
       ; e2 <- simpleExpression
       ; return(Under e1 e2)
       }
       
lambdaExpression =
    do{ reservedOp "\\"
      ; pats <- many1 simplePattern
      ; symbol "->"
      ; e <- expr
      ; return $ Lam pats e []
      }

ifExpression =
   do { reserved "if"
      ; e1 <- expr
      ; reserved "then"
      ; l1 <- getPosition
      ; e2 <- expr
      ; reserved "else"
      ; l2 <- getPosition
      ; e3 <- expr
      ; return $ ifExp (loc l1,loc l2) e1 e2 e3
      }


letExpression =
    do{ reserved "let"
      ; decls <- layout decl (reserved "in")
      ; xs <- mergeFun decls
      ; e <- expr
      ; return $ Let xs e
      }

circExpression = 
    do{ reserved "circuit"
      ; vs <- (parens(many name)) <|> return []
      ; e <- expr
      ; reserved "where"
      ; decls <- layout decl (return ())
      ; xs <- mergeFun decls
      ; return $ Circ vs e xs
      }

caseExpression =
    do{ reserved "case"
      ; e <- expr
      ; reserved "of"
      ; alts <- layout arm (return ())
      ; return $ Case e alts
      }

bodyP :: Parser a -> Parser (Body Exp)
bodyP equal = (fmap Guarded (many1 guard)) <|>
              (equal >> fmap Normal expr)
   where guard = do { try (symbol "|")
                    ; x <- expr
                    ; equal
                    ; y <- expr
                    ; return(x,y)}

whereClause =
      (do { reserved "where"
          ; ds <- layout decl (return ())
          ; xs <- mergeFun ds
          ; return xs})
  <|> (return [])

arm =
    do{ pos <- getPosition
      ; pat <- pattern
      ; e <- bodyP (symbol "->")
      ; ds <- whereClause
      ; return $ (loc pos,pat,e,ds)
      }

{- The actual opList function is defined in Syntax
opList prefix op =
    [ [ prefix "-", prefix "+" ]
    , [ op "." AssocLeft ]
    , [ op "^"  AssocRight ]
    , [ op "*"  AssocLeft, op "/"  AssocLeft ]
    , [ op "+"  AssocLeft, op "-"  AssocLeft ]
    , [ op ":" AssocRight ]
    , [ op "++" AssocRight ]
    , [ op "==" AssocNone, op "/=" AssocNone, op "<"  AssocNone
      , op "<=" AssocNone, op ">"  AssocNone, op ">=" AssocNone ]
    , [ op "&&" AssocNone ]
    , [ op "||" AssocNone ]
    , [ op "$" AssocRight ]
    ]
-}

operators = opList prefix op AssocLeft AssocRight AssocNone
    where
      op ":" assoc    = Infix (do{ var <- try (reservedOp ":")
                                 ; return consExp}) assoc
      op "$" assoc    = Infix (do{ var <- try (reservedOp "$")
                                 ; return (\x y -> binop "$" x y)}) assoc
      op "." assoc    = Infix (do{ var <- try (reservedOp ".")
                                 ; return (\x y -> binop "." x y)}) assoc
      op name assoc   = Infix (do{ var <- try (reservedOp name)
                                 ; return (\x y -> binop name x y)}) assoc
      prefix name     = Prefix(do{ var <- try (reservedOp name)
                                 ; return (buildPrefix name)
                                 })
                                 
buildPrefix :: String -> Exp -> Exp                                 
buildPrefix "-" (Lit (Int n)) = Lit(Int (-  n))                               
buildPrefix "-" (Lit (Float n)) = Lit(Float (-  n))
buildPrefix "#-" (Lit (Float n)) = Lit(Float (-  n))
buildPrefix "+" (Lit (Int n)) = Lit(Int n)                               
buildPrefix "-" x = App (Var (Global "negate")) x
buildPrefix "#-" x = App (Var (Global "negateFloat")) x
buildPrefix name x = App (Var (Global name)) x

infixExpression =
    buildExpressionParser ([[Infix p1 AssocLeft]] ++ operators) applyExpression
      where p1 = try (do { whiteSpace; (char '`');
                                v <- name;
		                (char '`');whiteSpace;
                                return (\x y -> App (App (Var  v) x) y) })
                             <?> "quoted infix operator"
     


applyExpression =
    do{ exprs <- many1 simpleExpression
      ; return (foldl1 App exprs)
      }

simpleExpression :: Parser Exp
simpleExpression =
        literal lit2Exp
    <|> try(around pExp aroundInfo) -- -- things like [1,2,3] (1,2) [| x+1 |]
    -- <|> try bracketExp
    <|> try escapeExp
    <|> section
    -- <|> parensORtuple expr expTuple
    -- <|> listExpression expr listExp -- things like [1,2,3]
    <|> caseExpression
    <|> sumExpression -- like (L x) or (R 3), Must precede expconstructor
    <|> try escapeExp
    <|> expconstructor
    <|> try natExp
    <|> expvariable            -- names last
    <?> "simple expression"
                    
-----------------------------------------------------------------------

escapeExp =
     lexeme (do { nm <- try (prefixIdentifier '$')  -- $x where x is a variable
                ; return(Escape(Var (Global nm)))})
 <|> (do { char '$'; char '('        -- $( ... ) where the $ and ( must be adjacent
         ; whiteSpace
         ; e <- expr; symbol ")"
         ; return (Escape e) })


bracketExp =
    do { reservedOp "[|"
       ; e <- expr
       ; reservedOp "|]"
       ; return (Bracket e) }


sumExpression =
  do { inj <- ((reserved "R" >> return True) <|> (reserved "L" >> return False))
     ; x <- expr
     ; let f True x = Sum R x
           f False x = Sum L x
     ; return (f inj x)
     }

section = try(do { symbol "("
                 ; z <- oper
                 ; symbol ")"
                 ; return (Lam [Pvar (Global "x"),Pvar (Global "y")]
                               (App (App (Var (Global z)) (Var (Global "x"))) (Var (Global "y"))) [])
                 })


draw =
 (do { pos <- getPosition
     ; reserved "let"
     ; decls <- layout decl (return ())
     ; xs <- mergeFun decls
     ; return(LetSt (loc pos) xs) }) <|>
 (try ( do { pos <- getPosition
           ; p <- pattern
           ; symbol "<-"
           ; e<-expr
           ; return(BindSt (loc pos) p e)})) <|>
 (do { pos <- getPosition; e <- expr; return(NoBindSt (loc pos) e)})

doexpr =
  do { reserved "do"
     ; zs <- layout draw (return ())
     ; return(Do zs)
     }

-------------------------------------------------------------------------
----------------- Read eval printloop commands ------------

data Command =
    ColonCom String String      -- :t x
  | LetCom Dec               -- let x = 5
  | DrawCom Pat Exp          -- x <- 6
  | ExecCom Exp              -- x + 4


pCommand :: Parser Command    -- Parse a command
pCommand =
  (try (do { symbol ":"; Global x <- name
           ; rest <- many (satisfy (\ x-> True))
           ; return (ColonCom x rest)}))
  <|>
  (try (do { reserved "let"; d <- decl; return(LetCom d)}))
  <|>
  (try (do { p <- pattern; symbol "<-"; e <- expr; return(DrawCom p e)}))
  <|>
  fmap ExecCom expr


----------------------------------------------------------------
-- the Parser for the haskell subset
----------------------------------------------------------------

program =
  do{ whiteSpace
    ; ds <- layout decl (return "")
    ; eof
    ; xs <- mergeFun ds
    ; return $ (Program xs)
    }


	
-----------------------------------------------------------
-- Declarations
-----------------------------------------------------------

decl = -- try fundecl
         try patterndecl -- Needs to be before vdecl
     <|> try typeSig
     <|> typeSyn
     <|> importDec
     <|> primDec
     <|> vdecl
     <|> datadecl
     <|> typeFunDec
    -- <|> kinddecl
     <|> flagdecl
     <|> monaddecl
     <|> testDec
     -- <|> typedecl
     -- <|> splicedecl
     -- <|> anddecl
     -- <|> protodecl
     <?> "decl"

testDec =
  do { testSym
     ; s <- stringLiteral
     ; ds <- layout decl (return ())
     ; xs <- mergeFun ds
     ; return(Reject s xs)
     }

flagdecl =
  do{ pos <- getPosition
    ; reserved "flag"
    ; flag <- name
    ; nm <- name
    ; return(Flag flag nm)
    }

vdecl =
  do{ pos <- getPosition
    ; ps <- many1 simplePattern
    ; e <- bodyP (reservedOp "=")
    ; ds <- whereClause
    ; toDecl (loc pos) (ps,e,ds)
    }

importDec =
  do { reserved "import"
     ; filename <- stringLiteral
     ; args <- parens (sepBy thing comma)
     ; return(Import filename args)
     }
  where thing = (name <|> (do { x <- parens operator;return(Global x)}))
  
typeSig =
   do{ pos <- getPosition
     ; n <- (constructorName <|> name)
     ; reservedOp "::"
     ; t <- typN 0
     ; return $ TypeSig (loc pos) n t }

typeSyn = 
   do{ pos <- getPosition
     ; reserved "type"
     ; Global n <- constructorName
     ; args <- targs 0
     ; reservedOp "="
     ; t <- typN 0
     ; return $ TypeSyn (loc pos) n args t }

typeFunDec = 
   do{ pos <- getPosition
     ; (f,xs) <- braces args
     ; reservedOp "="
     ; body <- typN 0
     ; return(TypeFun (loc pos) f Nothing [(xs,body)])}
  where args = do { Global f <- name
                  ; zs <- many1 (simpletyp 0)
                  ; return(f,TyVar' f : zs) }
                                 
     
     
primDec =
   do{ pos <- getPosition
     ; reserved "primitive"
     ; n <- (name <|> parens operator)
     ; reservedOp "::"
     ; t <- typN 0
     ; return $ Prim (loc pos) n t }
 where operator = 
          do { cs <- many (opLetter tokenDef)
             ; return(Global cs) }

patterndecl =
  do { pos <- getPosition
     ; symbol "pattern"
     ; c <- constructorName
     ; xs <- many name
     ; reservedOp "="
     ; p <- pattern
     ; return(Pat (loc pos) c xs p)}

monaddecl =
   do{ pos <- getPosition
     ; reserved "monad"
     ; e <- expr
     ; return(monadDec (loc pos) e)}
  
datadecl =
  do{ pos <- getPosition
    ; (strata,prop) <- (reserved "data" >> return(0,False)) <|>
                       (reserved "prop" >> return(0,True)) <|>
                       (reserved "kind" >> return(1,False))
    ; t <- name
    ; explicit prop pos t <|> implicit prop pos strata t
    }
 
implicit b pos strata t =
  do{ args <- targs 0
    ; reservedOp "="
    ; let finish cs ds = Data (loc pos) b strata t Nothing args cs ds
    ; (reserved "primitive" >> return(finish [] [])) <|>
      (do { cs <- sepBy1 (constrdec 0) (symbol "|")
          ; ds <- derive
          ; return(finish cs ds)})
    }

 
explicit b pos tname = 
  do { symbol "::"
     ; kind <- typN 1
     ; reserved "where"
     ; cs <- layout explicitConstr (return ())
     ; let gadt = (GADT (loc pos) b tname kind cs)
     ; case (okGADT gadt) of
        Nothing -> return(transGADT gadt)
        Just s -> fail s
     }

explicitConstr = 
  do { l <- getPosition
     ; c <- constructorName
     ; symbol "::"
     ; preds <- props 0
     ; domain <- typN 0
     ; return(loc l,c,preds,domain)
     }

targs strata = many arg
  where arg = simple <|> parens kinded
        simple = do { n <- name; return(n,AnyTyp (strata+1)) }
        kinded = do { n <- name; symbol "::"
                    ; t<- typN strata
                    ; return(n,t)}
      
kinddecl =
  do{ pos <- getPosition
    ; reserved "kind"
    ; t <- name
    ; args <- many name
    ; reservedOp "="
    ; cs <- sepBy1 pairs (symbol "|")
    ; return (Kind (loc pos) t args cs)
    }
 where pairs = do{ c <- constructorName
                 ; domain <- many (simpletyp 1)
                 ; return (c,domain)}


derive =
  (do { reserved "deriving"
      ; (do {c <- constructorName; return [c]}) <|>
        (parens(sepBy1 constructorName (symbol ","))) })
  <|> (return [])

constrdec strata =
 do{ pos <- getPosition
   ; exists <- (forallP strata <|> (return []))
   ; c <- constructorName
   ; domain <- many (simpletyp strata)
   ; eqs <- possible (reserved "where" >> sepBy1 (proposition strata) (symbol ","))
   ; return (Constr (loc pos) exists c domain eqs)
   }

forallP strata =
 do { (reserved "forall") <|> (reserved "exists") <|> (symbol "ex" >> return ())
    ; ns <- targs strata
    ; symbol "."
    ; return ns
    }


toDecl pos ((Pvar f : (args @ (p:ps))),body,ws) = return(Fun pos f Nothing [(pos,args,body,ws)])
toDecl pos ([p],b,ws) = return(Val pos p b ws)
toDecl pos (ps,b,ws) = fail ("Illegal patterns to start value decl:" ++(show ps))




-------------------------------------------------------------
-- Unused stuff from the cannabalized parser
{-
protodecl =
  do { nm <- name; symbol "::"; t <- typ; return(Proto nm t) }

anddecl =
  do { reserved "and"; return (Bndgrp[]) }

splicedecl =
  do { reserved "splice"
     ; e <- expr
     ; return(Splice e)
     }


patdecl =
  do{ pos <- getPosition
    ; pat <-  pattern
    ; e <- bodyP (reservedOp "=")
    ; ds <- whereClause
    ; return (Val (loc pos) pat e ds)
    }

fundecl =
  do{ pos <- getPosition
    ; ms <- many1 matchp
    ; return (Fun (loc pos) (fst(head ms)) Nothing (map snd ms))
    }

matchp =
  do { pos <- getPosition
     ; f <- name
     ; ps <- many1 pattern
     ; e <- bodyP (reservedOp "=")
     ; ds <- whereClause
     ; return (f,(loc pos,ps,e,ds))
     }



-----------------------------------------------------------
-- Expressions
-----------------------------------------------------------
-- Uused expressions like do and comprehensions


-----------------------------------------------------------
-- Infix expression
-----------------------------------------------------------



reifier = (reserved "line" >> return Line) <|>
          (reserved "type" >> terminal name Typeof) <|>
          (reserved "rep" >> terminal name Repof)




codeExpression = (bracket "[|" "|]" Exclam expr) <|>
                 (bracket "<." ".>" Period pattern) <|>
                 (bracket "<$" "$>" Dollar decl) <|>
                 (bracket "<*" "*>" Times typ) <|>
                 (keyBr "e" Exclam expr) <|>
                 (keyBr "d" Dollar decl) <|>
                 (keyBr "p" Period pattern) <|>
                 (keyBr "t" Times typ) <|>
                 (keyBr "m" Match arm) <|>
                 (keyBr "c" Clause (fmap snd matchp))
  where bracket l r inject p =
           try(between(reservedOp l)(reservedOp r)(fmap (Brack . inject) p))
        keyBr key inject p =
           try(between(reserved ("["++key++"|"))(symbol "|]")(fmap (Brack . inject) p))



escExpression =
  (do { symbol "$"
      ; x <- expvariable <|> (parens expr) <|> codeExpression
      ; return(Esc x) })



-------------------------------
-- Try and parse things that are surrounded by []'s like:
-- []
-- [1,2,3]
-- [ x | c <- y ]
-- [1..] or [1,2..] or [1..3] or [1,2..6]

-- expList (explicit List) is a finite state machine
expList = do { try open; one }
  where open = symbol "["
        close = symbol "]"
        bar = symbol "|"
        dots = symbol ".."
        one   = (do { try close; return nilE}) <|>
                (do { e <- expr; two e })
        two e = (do { try close; return(listExp[e])})
            <|> (do { try comma; e2 <- expr; three e e2 })
            <|> (do { try dots; four e })
            <|> (do { try bar; ss <- rest comma draw []
                    ; return(Comp(ss ++ [ NoBindSt e ]))})
        three a b = (do { try comma; es <- rest comma expr [b,a]
                        ; return(listExp es)})
                <|> (do { try dots
                        ; (try close >> return(ArithSeq(FromThen a b))) <|>
                          (do { c <- expr; close
                              ; return(ArithSeq(FromThenTo a b c))})
                        })
                <|> (try close >> return(listExp[a,b]))
        four e = (try close >> return(ArithSeq(From e)))
             <|> (do{ e2 <- expr; close; return(ArithSeq(FromTo e e2))})

-- look for:  p sep p sep p ]
rest sep p xs =
  (do { try (symbol "]"); return(reverse xs)}) <|>
  (do { x <- p
      ; (try (symbol "]") >> return(reverse(x:xs))) <|>
        (do { sep; rest sep p (x:xs)})
      })


--h ::  Int -> IO (Either ParseError [Dec])
pf x = do { z <- parseFromFile program x
          ; putStrLn (show z)
          }

h x = pf "testParser.tst"

m () = parse2 expr "let x=4\n    f y = 3\n     in 3"

-}


testdata = concat
	["data Rep e t"
	,"  = Int (Equal t Int)"
	,"  | Char (Equal t Char)"
	,"  | Var (forall a . e -> Rep a t)"
	,"  | forall a b . Pair (Rep e a) (Rep e b) (Equal t (a,b))"
	,"  | forall a b . Arr (Rep e a) (Rep e b) (Equal t (a -> b))"
	,"  | forall a b . Back (Rep e a) (Rep e b) (Equal t (From a b))"
	,"  | forall f . Univ (forall x . (Rep (P x e) (f x))) (Equal t (Poly f))"
	]
	
(Right(d1,_)) = pd testdata	


d2 = pd "f = \\ n -> if n==0 then True else n * (fact (n-1))"

d3 = pd "v (f,_) = V f\n\ngam r e = Lam r e self"

d4 = pd "test :: forall a b . a -> (a,b)"

Right(e1,_) = pe "do { y <- tim; x <- poly ; x }"

prim1 :: Dec
Right(prim1,_) = pd "f x = do { y <- Just 3; return(y + x) }"

Right(do1,_) = pe "do { y <- Just 3; return(y + x) }"

Just e2 = (getExp "let {(u,v) = f x;(a,b) = g v } in u")
gete x = unJust(getExp x) where unJust(Just z) = z


transvar :: Int -> [(Var,(Int,Int))] -> Var -> Exp
transvar n sigma s =
  case (n,lookup s sigma) of
    (0,Nothing) -> Var s
    (1,Nothing) -> App (var "Lit") (Var s)
    (0,Just(0,delta)) -> lift s sigma (Var s)
    (1,Just(0,delta)) -> App (var "Lit") (Var s)
    (0,Just(1,delta)) -> error ("Var "++show s++" used too early")
    (1,Just(1,delta)) -> App (var "V") (deBruijn delta)
 where deBruijn 0 = var "z"
       deBruijn n = App (var "s") (deBruijn (n-1))
       lift s [] exp = exp
       lift s ((x,(lev,delta)):zs) exp =
           if s==x then exp
                   else if lev <= 0 then lift s zs exp
                                    else lift s zs (App (var "liftExp") exp)


extend s n zs = (s,(n,0)) : map f zs  where f(s,(lev,c)) = (s,(lev,c+1))

test s = case getExp s of
           Just e -> trans 0 [] e
           Nothing -> error ("Parsing error for: "++s)

trans 0 sigma x =
  case x of
    Var s -> transvar 0 sigma s
    Lit v -> Lit v
    Lam [Pvar s] b xs -> Lam [Pvar s] (trans 0 (extend s 0 sigma) b) xs
    App x y -> App (trans 0 sigma x) (trans 0 sigma y)
    Prod x y -> Prod (trans 0 sigma x) (trans 0 sigma y)
    Let [Val loc (Pvar s) (Normal e) []] b ->
      Let [Val loc (Pvar s) (Normal (trans 0 sigma e)) []] (trans 0 (extend s 0 sigma) b)
    Let [Fun l1 nm h1 [(l2,[Pvar x],Normal e,[])]] w ->
      Let [Fun l1 nm h1 [(l2,[Pvar x],Normal (trans 0 (extend x 0 (extend nm 0 sigma)) e),[])]]
          (trans 0 (extend nm 0 sigma) w)
    Case x [(l1,Pcon (Global "True") [],Normal y,[]),(l2,Pcon (Global "False") [],Normal z,[])] ->
       Case (trans 0 sigma x)
           [(l1,Pcon (Global "True") [],Normal (trans 0 sigma y),[])
           ,(l2,Pcon (Global "False") [],Normal(trans 0 sigma z),[])]

    Bracket e -> trans 1 sigma e
    other -> error ("No translation at level 0 for "++(show x))
trans 1 sigma x =
  case x of
    Var s -> transvar 1 sigma s
    Lit (Int n) -> lit x
    Lit (Char c) -> lit x
    Lit Unit -> App (var "Unit") (var "self")
    Lam [Pvar s] b  xs -> lam (trans 1 (extend s 1 sigma) b)
    App (App (Var (Global "+")) x) y -> plus (trans 1 sigma x) (trans 1 sigma y)
    App (App (Var (Global "*")) x) y -> times (trans 1 sigma x) (trans 1 sigma y)
    App x y -> app (trans 1 sigma x) (trans 1 sigma y)
    Prod x y -> prod (trans 1 sigma x) (trans 1 sigma y)
    Let [Val loc (Pvar s) (Normal e) []] b -> mkLet (trans 1 sigma e) (trans 1 (extend s 1 sigma) b)
    Case x [(_,Pcon (Global "True") _,Normal y,_),(_,Pcon (Global "False") _,Normal z,_)] ->
        mkif (trans 1 sigma x) (trans 1 sigma y) (trans 1 sigma z)
    --Escape(Var s) ->
    Escape e -> trans 0 sigma e
    other -> error ("No translation at level 1 for "++(show x))
 where lit x = apply[var "Lit", x]
       app x y = apply [var "App",x,y]
       lam body = apply [var "Abs",body,self]
       mkLet e b = apply [var "Let",e,b]
       mkif x y z = apply[var "Comp",var "==",x,y,z]
       prod x y = apply [var "Pair",x,y,self]
       plus x y = apply [var "Arith",var "+",x,y,self]
       times x y = apply [var "Arith",var "*",x,y,self]
       apply [x] = x
       apply (f:x:xs) = apply (App f x : xs)
       self = var "self"

b1 = test "[| \\ x -> x |]"
b2 = test "[| \\ x -> x + 1 |]"
b3 = test "\\ f -> [| \\ y -> f y |]"
b4 = test "\\ f -> [| \\ y -> $f y |]"
b5 = test "\\ f -> [| \\ y -> \\ z -> $f y |]"
b6 = test "\\ f -> [| \\y -> $( (\\w -> [| $f $w |])   ( [| y + 1|] )) |]"
b7 = test "\\ f -> [| \\y -> $( (\\z -> [| \\ q -> $f $z |])   ( [| y |] )) |]"
b8 = test "let f x = \\ e -> if x==0 then e else [| let n = x in $(f (x-1) [| n + $e |]) |] in f 2"

tr :: String -> IO ()
tr s = case getExp s of
         Just e -> do { y <- freshE e; x <- (swp y); putStr(show x) }
         Nothing -> error ("Parsing error for: "++s)


----------------------------------------------------


z1 = pd 
  "id :: forall (k:: *1) (a:: *) . a -> a\nid x = x"

z2 = parse2 (allTyp 0) "forall (a:: * ) b . a -> (a,b)"


Right(z4,_) = pd "data Var:: *0 ~> *0 ~> *0 where \n  Z:: Var (w,x) w\n  S:: Var w x -> Var (y,w) x"



--code for parsing an explicit without translation for debugging
completeExplicit = 
  do { pos <- getPosition
     ; strata <- (reserved "data" >> return 0) <|>
                  (reserved "kind" >> return 1)
     ; tname <- name
     ; symbol "::"
     ; kind <- typN 1
     ; reserved "where"
     ; cs <- layout explicitConstr (return ())
     ; return (GADT (loc pos) False tname kind cs)
     }
     
Right(z3,_) = parse2 completeExplicit 
  ("data Decs :: Ctype ~> Row HasType ~> Row HasType ~> *0 ~> *0 where\n"++
   "  In :: (Exp c all t) -> Decs c all all t\n")
look = putStr(show (transGADT z3))

Right(z5,_) = pd "data Exp:: *0 ~> *0 ~> *0 ~> *0 ~> *0 where\n Const:: t -> Exp past now future t\n Run:: (forall n . Exp past now (n,future) (Cd n future t)) -> Exp past now future t"




zz = pe "(Decl `inpz )"
 

dd = GADT (SrcLoc 1 1) False (Global "Decs") 
  (Karrow' (TyCon' "Ctype") 
  (Karrow' (TyApp' (TyCon' "Row") (TyCon' "HasType")) 
  (Karrow' (TyApp' (TyCon' "Row") (TyCon' "HasType")) 
  (Karrow' (Star' 0) (Star' 0))))) 
  [(SrcLoc 2 3,Global "In",[],Rarrow' (TyApp' (TyApp' (TyApp' (TyCon' "Exp") (TyVar' "c")) (TyVar' "all")) (TyVar' "t")) (TyApp' (TyApp' (TyApp' (TyApp' (TyCon' "Decs") (TyVar' "c")) (TyVar' "all")) (TyVar' "all")) (TyVar' "t")))]
