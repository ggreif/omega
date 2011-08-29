module ParserDef (pp,pe,pd,name,getExp,getInt,getBounds,
                pattern,expr,decl,
                program,parse2,parse,parseString,parseFile
                ,parseHandle, Handle
                ,Command(..),pCommand
                ,d1)
                where

-- To import ParserAll you must define CommentDef.hs and TokenDef.hs
-- These should be in the same directory as this file.

import System.IO.Unsafe(unsafePerformIO)

import ParserAll
import Syntax(Exp(..),Pat(..),Body(..),Lit(..),Inj(..),Program(..)
             ,Dec(..),Constr(..),Stmt(..),Var(..)
             ,listExp,listExp2,patTuple,ifExp,mergeFun,consExp,expTuple
             ,binop,opList,var,freshE,swp,dvars,evars,
             typeStrata,kindStrata,emptyF,Vars(..),boundBy
             ,monadDec,Derivation(..),ImportItem(..),FX(..),typVar)
import List(partition)
import Monads
import RankN(PT(..),typN,simpletyp,proposition,pt,allTyp
            ,ptsub,getFree,parse_tag,props,typingHelp,typing,conName,arityPT)
import SyntaxExt  -- (Extension(..),extP,SynExt(..),buildNat,pairP)
import Auxillary(Loc(..),plistf,plist)
import Char(isLower,isUpper)
---------------------------------------------------------

loc p = SrcLoc (sourceName p) (sourceLine p) (sourceColumn p)

-------------------------------------------------------------
-- Parsers exported, and those defined for easy testing

go s = parse expr "" s
g s = parse pattern "" s
f p s = parse p "" s
pp = parse2 pattern
pe = parse2 expr
pd = parse2 decl

pds = parse2(layout decl (return ""))

p2 p s = case parse2 p s of
  Left s -> putStrLn s
  Right (x,left) -> putStrLn (show x) >> putStrLn left

pa = parse2 arm

getInt :: Monad m => (String -> m Int) -> String -> m Int
getInt failf s = case parse2 natural s of
              Left s -> failf s
              Right(n,s) -> return(fromInteger n)

getBounds::  Monad m => (String -> m (String,Int)) -> String -> m (String,Int)
getBounds failf "" = return("",0)
getBounds failf s =
   case parse2 bounds s of
      Left s -> failf (message ++ s)
      Right(n,s) -> return n
  where bounds = do { s <- identifier
                    ; n <- natural
                    ; return(s,fromInteger n)}
        message = "\nIllegal bounds argument. Should be something like\n  "++
                  ":bounds narrowing 25\nUse :bounds with no argument to see legal bounds arguments.\n\n"

getExp :: Monad m => String -> m Exp
getExp s = case pe s of
             Left s -> fail s
             Right(exp,rest) -> return exp

pprog x = parseFromFile program x

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

parseHandle p s h = comp
  where comp =  do { x <- parseFromHandle p s h
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

-- Map the temporary type to the Exp type.
lit2Exp (LInt n) = Lit(Int n)
lit2Exp (LChar c) = Lit(Char c)
lit2Exp (LString s) = listExp (map (Lit . Char) s)
lit2Exp (LChrSeq s) = Lit(ChrSeq s)
lit2Exp (LFloat n) = Lit(Float (doubleToFloat n))
lit2Exp (LTag n) = Lit(Tag n)

doubleToFloat :: Double -> Float
doubleToFloat n = encodeFloat a b
  where (a,b) = decodeFloat n

-----------------------------------------------------------
-- Terminals of the grammar. I.e. Literals, variables, and constructors
-----------------------------------------------------------

literal :: (Literal -> a) -> (Extension a -> a) -> Parser a
literal fromLit fromExt = lexeme
   (try (fmap fromLit floatLit) <|>  -- float before natP or 123.45 leaves the .45
    try (fmap fromExt natP) <|>
    try (fmap fromLit (chrSeqLit <|> chrLit <|> strLit <|> atomLit))
    <?> "literal")

chrSeqLit = do{ satisfy ('#'==); s <- stringLiteral; return(LChrSeq s)}
chrLit  = do{ c <- charLiteral; return (LChar c) }
strLit  = do{ s <- stringLiteral; return(LString s) }
atomLit = parse_tag LTag
floatLit = do { n <- float; return(LFloat n)}

literalP = literal lit2Pat extToPat
literalE = literal lit2Exp extToExp

numLiteral =
  do { n <- naturalOrFloat
     ; case n of
         Left i -> return (LInt (fromInteger i))
         Right r -> return(LFloat r) }

signedNumLiteral =
  do { let neg (LInt i) = (LInt(negate i))
           neg (LFloat i) = (LFloat(negate i))
     ; sign <- (char '-' >> return neg)<|>(char '+' >> return id)<|>(return id)
     ; n <- numLiteral
     ; return(sign n)}


terminal p inject = do { v <- p; return (inject v)}

expvariable,expconstructor :: Parser Exp
expvariable = terminal identifier (Var . Global)

conNameUnreserved = conName >>= \s -> if isReservedName s then
                                      fail ("reserved name '"++s++"' must not appear here")
                                      else return s
expconstructor = terminal conNameUnreserved prepareCon
                   where prepareCon "L" = buildLambda L
                         prepareCon "R" = buildLambda R
                         prepareCon s = var s
                         buildLambda s = Lam [Pvar (Global "x")] (Sum s $ var "x") []
                         var = Var . Global

patvariable :: Parser Pat
patvariable = do { (result@(Pvar x)) <- terminal identifier (Pvar . Global)
                 ; let (Global (patname@(init:_))) = x
                 ; if isUpper init
                   then fail ("pattern bindings must be lowercase, but this is not: " ++ patname)
                   else return result}
name,constructor :: Parser Var
constructor = terminal conName Global
name = terminal identifier Global



-----------------------------------------------------------
-- Syntactic Extensions
-- They come with or without suffixes. Without suffixes they are
-- the standard kind of syntactic sugar
--
-- type     no-suffix        with suffix
-----------------------------------------------------------
-- Numbers  23               9i   (2+n)i
-- Ticked   (var`2)          (var`2)i
-- Lists    [2,3]            [3,4]i  [3,4,5; x]i
-- Tuples   (2,True)         (2,True,"x")i
-- Records  {a=4, b=True}    {a=Int, b=Bool}r  {a=Int; r}r
-- Items                     (x)i
-- Units                     ()i
-----------------------------------------------------------
-- Left{List,Pair,Record} are the left-associative variants
--

-- If a syntactic extension has the empty string as a suffix
-- turn it into the normal kind of syntactic sugar

extToExp (Pairx (Right xs) "") = expTuple xs
extToExp (Listx (Right xs) Nothing "") = listExp xs
extToExp (Listx (Right xs) (Just tail) "") = listExp2 xs tail
extToExp (Natx n Nothing "") = Lit(Int n)
extToExp (Natx n (Just exp) "") = App (App (Var (Global "+")) (Lit(Int n))) exp
extToExp x = ExtE x

extToPat (Pairx (Right xs) "") =  patTuple xs
extToPat (Listx (Right xs) Nothing "") =  pConsUp patNil xs
extToPat (Listx (Right xs) (Just tail) "") =  pConsUp tail xs
extToPat (Natx n Nothing "") = Plit(Int n)
extToPat x = ExtP x

patNil = Pcon (Global "[]") []
pConsUp pnil [] = pnil
pConsUp pnil (p:ps) = Pcon (Global ":") [p,pConsUp pnil ps]

-------------------------------------------------------------
-- Pattern parsing

pattern =
      try asPattern
  <|> try (do { p <- (try conApp <|> simplePattern); symbol "::"; t <- typN; return(Pann p t)})
  <|> try infixPattern
  <|> conApp
  <|> simplePattern
  <?> "pattern"

asPattern =
  do { Pvar x <- patvariable
     ; symbol "@"
     ; p <- pattern
     ; return (Paspat x p)
     }

infixPattern =
  do { p1 <- try conApp <|> simplePattern
                    --  E.g. "(L x : xs)" should parse as ((L x) : xs) rather than (L(x:xs))
     ; x <- constrOper
     ; p2 <- pattern
     ; return (Pcon (Global x) [p1,p2])
     }

failUnaryPcon con = fail ("unary pattern constructor '" ++ con
                          ++ "' used where a nullary one is expected (did you mean '("
                          ++ con ++ " p)'?)")
nullaryPcon (Global "L") = failUnaryPcon "L"
nullaryPcon (Global "R") = failUnaryPcon "R"
nullaryPcon (Global "Ex") = failUnaryPcon "Ex"
nullaryPcon nm = return $ Pcon nm []

simplePattern :: Parser Pat
simplePattern =
        literalP
    <|> (do { p <- extP pattern; return(extToPat p)})
    <|> (try (fmap lit2Pat (parens signedNumLiteral)))
    <|> (do { symbol "_"; return Pwild})
    <|> (do { nm <- constructor; nullaryPcon nm })
    <|> patvariable
    <?> "simple pattern"

conApp =
   (do { name <- constructor
      ; ps <- many simplePattern
      ; return (pcon name ps)})

pcon (Global "L") [p] = Psum L p
pcon (Global "R") [p] = Psum R p
pcon (Global "Ex") [p] = Pexists p
pcon n ps = Pcon n ps

resOp x = reservedOp x >> return ""

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
lit2Pat (LString s) = pConsUp patNil (map (Plit . Char) s)


-----------------------------------------------------------
-- Expressions
-----------------------------------------------------------

-- simple expressions are one token, or surrounded by bracket-like things
simpleExpression :: Parser Exp
simpleExpression =
        literalE                  -- "abc"   23.5   'x'   `d  123  #34 45n
    <|> code                      -- [| 3 + x |]
    <|> try escapeExp             -- $x  $(f 3)
    <|> pairOper                  -- (,)
    <|> section                   -- (+)
    <|> caseExpression
    <|> expconstructor            -- Node Cons
    <|> fmap extToExp (extP expr) -- Syntax extensions, like
                                  -- (2,True)p [3,4,5]l {`a=5,`b=True}r
                                  -- see literalE (above) for things like #4 and 5i
    <|> expvariable               -- names come last
    <?> "simple expression"


expr :: Parser Exp
expr =  lambdaExpression
    <|> letExpression
    <|> circExpression
    <|> ifExpression
    <|> doexpr
    <|> try (do { p <- simpleExpression; symbol "::"
                ; t <- typN
                ; return(Ann p t)})
    <|> infixExpression     --names last
    <?> "expression"

-- 123  #34 45n
num = lexeme(try (do { n <- natP; return(extToExp n)}))

-- (,)
pairOper = (try (string "(,)" >> return(Var (Global "(,)"))))


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
              (equal >> ((reserved "unreachable" >> return Unreachable) <|>
                         (fmap Normal expr)))
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


section = try(do { symbol "("
                 ; z <- oper
                 ; symbol ")"
                 ; return (Lam [Pvar (Global "x"),Pvar (Global "y")]
                               (App (App (Var (Global z))
                                    (Var (Global "x")))
                                         (Var (Global "y"))) [])
                 })


draw = letD <|> bind <|> exp where
 letD = do { pos <- getPosition
           ; reserved "let"
           ; decls <- layout decl (return ())
           ; xs <- mergeFun decls
           ; return(LetSt (loc pos) xs) }
 bind = try $
        do { pos <- getPosition
           ; p <- pattern
           ; symbol "<-"
           ; e<-expr
           ; return(BindSt (loc pos) p e)}
 exp  = do { pos <- getPosition; e <- expr
           ; return(NoBindSt (loc pos) e)}

doexpr =
  do { reserved "do"
     ; zs <- layout draw (return ())
     ; return(Do (Var (Global "bind"), Var (Global "fail")) zs)
     }

----------------------------------------------------
-- Infix operators

{- The actual opList function is defined in Syntax
opList prefix op left right none =
    [ [ prefix "-", prefix "+", prefix "#-" ]
    , [ op "!!" left]
    , [ op "^"  right]
    , [ op "*"  left, op "/"  left, op "#*"  left, op "#/"  left]
    , [ op "+"  left, op "-"  left, op "#+"  left, op "#-"  left]
    , [ op ":" right]
    , [ op "++" right]
    , [ op "==" none, op "/=" none, op "<"  none
      , op "<=" none, op ">"  none, op ">=" none
      , op "#==" none, op "#/=" none, op "#<"  none
      , op "#<=" none, op "#>"  none, op "#>=" none]
    , [ op "&&" none ]
    , [ op "||" none ]
    , [ op "<|>" right , op "<!>" right ]
    , [ op "$" right ]
    , [ op "." left]
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
    buildExpressionParser ([[Infix quotedInfix AssocLeft]] ++ operators) applyExpression

tryEtaOnSum (Lam [Pvar (Global "x")] (Sum s (Var (Global "x"))) []) a = Sum s a
tryEtaOnSum f a = App f a

applyBuiltin builtin (arg1:rest) = return $ foldl1 App (builtin arg1:rest)

assembleApply (Left "Ex") args@(_:_) = applyBuiltin Exists args
assembleApply (Left "check") args@(_:_) = applyBuiltin CheckT args
assembleApply (Left "lazy") args@(_:_) = applyBuiltin Lazy args
assembleApply (Left f) [] = fail ("builtin '"++f++"' must be applied to an argument")
assembleApply (Right f) args = return (foldl1 tryEtaOnSum (f:args))

reservedFun name = reserved name >> return name
reservedFuns = reservedFun "Ex" <|> reservedFun "check" <|> reservedFun "lazy"

applyExpression =
    do { fun <- fmap Left reservedFuns <|> fmap Right simpleExpression
       ; args <- many simpleExpression
       ; assembleApply fun args
       }

-- `mem`  `elem`
quotedInfix = try
 ((do { whiteSpace
      ; (char '`')
      ; v <- name
      ; (char '`')
      ; whiteSpace;
      ; return (\x y -> App (App (Var  v) x) y) }) <?> "quoted infix operator")

-----------------------------------------------------------------------
-- Syntax for building code

escapeExp = escVar <|> escParen  where
  escVar = do { nm <- (prefixIdentifier '$')  -- $x
              ; return(Escape(Var (Global nm)))}
  escParen = do { char '$'; char '('          -- $( ... )
                ; whiteSpace                  -- where the $ and ( must be adjacent
                ; e <- expr; symbol ")"
                ; return (Escape e) }

-- [| 3 + x |]
code =
  do { resOp "[|"
     ; e <- expr
     ; resOp "|]"
     ; return(Bracket e)}

-------------------------------------------------------------------------
----------------- Read-eval-print loop commands ------------

data Command =
    ColonCom String String   -- :t x
  | LetCom Dec               -- let x = 5
  | DrawCom Pat Exp          -- x <- 6
  | ExecCom Exp              -- x + 4
  | EmptyCom


instance Show Command where
  show (ColonCom t x) = ":"++t++" "++x
  show (LetCom d) = "let "++show d
  show (DrawCom p e) = show p++" <- "++show e
  show (ExecCom e) = show e
  show EmptyCom = ""

pCommand :: Parser Command    -- Parse a command
pCommand =
  (try (eof >> return EmptyCom))
  <|>
  (try (do { symbol ":"
           ; x <- lexeme(identifier <|> string "kind" <|> string "type")
           ; rest <- many (satisfy (\ x-> True))
           ; return (ColonCom x rest)}))
  <|>
  (try (do { symbol ":"; symbol "?"; return(ColonCom "?" "")}))
  <|>
  (try (do { reserved "let"; d <- decl; return(LetCom d)}))
  <|>
  (try (do { p <- pattern; symbol "<-"; e <- expr; return(DrawCom p e)}))
  <|>
  fmap ExecCom expr


----------------------------------------------------------------
-- the Parser for Omega programs
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

decl =   try patterndecl -- Needs to be before vdecl
     <|> try typeSig
     <|> typeSyn
     <|> importDec
     <|> primDec
     <|> try testDec -- Needs to be before vdecl
     <|> vdecl
     <|> datadecl
     <|> typeFunDec
     <|> flagdecl
     <|> monaddecl
     <|> theoremDec
     <?> "decl"

theoremDec =
  do{ pos <- getPosition
    ; reserved "theorem"
    ; vs <- sepBy theorem comma
    ; return(AddTheorem (loc pos) vs)
    }

theorem =
  do { v <- name
     ; term <- (try (do {reservedOp "="; e <- expr; return(Just e)})) <|> (return Nothing)
     ; return(v,term)}

testDec =
  do { lexeme (string "##test")
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
    ; toDecl (loc pos) (ps,e,ds) }
  where toDecl pos ((Pvar f : (args @ (p:ps))),body,ws) = return(Fun pos f Nothing [(pos,args,body,ws)])
        toDecl pos ([p],b,ws) = return(Val pos p b ws)
        toDecl pos ((Pcon c []):ps,b,ws) = return(Val pos (Pcon c ps) b ws)
        toDecl pos (ps,b,ws) = fail ("Illegal patterns to start value decl:" ++(show ps))

importDec =
  do { reserved "import"
     ; filename <- stringLiteral
     ; args <- (fmap Just (parens (sepBy thing comma))) <|> (return Nothing)
     ; return(Import filename args)
     }
  where thing = (deriv <|> var <|> oper)
        var =  do { n <- name; return(VarImport n)}
        oper = do { x <- parens operator; return(VarImport (Global x))}
        deriv = do { try(symbol "syntax")
                   ; Global n <- name
                   ; Global tag <- parens name
                   ; return (SyntaxImport n tag)}


typeSig =
   do{ pos <- getPosition
     ; ns <- (fmap (return . Global) conName <|> (sepBy name comma))
     ; (levels,t) <- typing
     ; return $ TypeSig (loc pos) ns (polyLevel levels t) }

typeSyn =
   do{ pos <- getPosition
     ; reserved "type"
     ; n <- conName
     ; args <- targs
     ; reservedOp "="
     ; t <- typN
     ; return $ TypeSyn (loc pos) n args t }

typeFunDec =
   do{ pos <- getPosition
     ; (f,xs) <- braces args
     ; reservedOp "="
     ; body <- typN
     ; return(TypeFun (loc pos) f Nothing [(xs,body)])}
  where args = do { Global f <- name
                  ; zs <- many1 simpletyp
                  ; return(f,TyVar' f : zs) }

primDec =
   do{ pos <- getPosition
     ; reserved "primitive"
     ; n <- (name <|> parens operator)
     ; (levels,t) <- typing
     ; return $ Prim (loc pos) n (polyLevel levels t) }
 where operator =
          do { cs <- many (opLetter tokenDef)
             ; return(Global cs) }

patterndecl =
  do { pos <- getPosition
     ; symbol "pattern"
     ; c <- conName
     ; xs <- many name
     ; reservedOp "="
     ; p <- pattern
     ; return(Pat (loc pos) (Global c) xs p)}

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
    ; t <- conName;
    ; (explicit prop pos (Global t)) <|> 
      (implicit prop pos strata (Global t))
    }

implicit b pos strata t =
  do{ args <- targs
    ; reservedOp "="
    ; let finish cs ds = Data (loc pos) b strata t Nothing args cs ds 
          kindf [] = Star' strata Nothing
          kindf ((_,x):xs) = Karrow' x (kindf xs)
    ; (reserved "primitive" >> return(GADT (loc pos) b t (kindf args) [] [] Ox)) <|>
      (do { cs <- sepBy1 constrdec (symbol "|")
          ; ds <- derive (map getCArity1 cs)
          ; return(finish cs ds)})
    }


getCArity1 (Constr loc args (Global c) domains _) = (c,length domains)
getCArity2 (loc,(Global c),args,constraints,typ) = (c,arityPT typ)

polyLevel [] t = t
polyLevel xs t = PolyLevel xs t

explicit b pos tname =
  do { (levels,kind) <- typing
     ; reserved "where"
     ; cs <- layout explicitConstr (return ())
     ; ds <- derive (map getCArity2 cs)
     ; let gadt = (GADT (loc pos) b tname (polyLevel levels kind) cs ds Ox)
     ; return(gadt)
     }

explicitConstr =
  do { l <- getPosition
     ; c <- conName
     ; (levels,prefix,preds,body) <- typingHelp  -- ### TODO LEVEL
     ; let format Nothing = []
           format (Just(q,kindings)) = map g kindings
           g (nm,kind,quant) = (nm,kind)
     ; return(loc l,Global c,format prefix,preds,body)
     }

targs = many arg
  where arg = simple <|> parens kinded
        simple = do { n <- name; return(n,AnyTyp) }
        kinded = do { n <- name; symbol "::"
                    ; t<- typN
                    ; return(n,t)}

-- Deriving clauses, both new and old style

derive :: [(String,Int)] -> Parser [Derivation]
derive arityCs =
  (do { reserved "deriving"
      ; (do {c <- extension arityCs ; return [c]}) 
      })
  <|> (return [])

extension arityCs = (try (newStylePx arityCs)) <|> (oldStylePx arityCs)

oldStylePx arityCs =
  do { name <- conName 
     ; tag <- parens(many (lower <|> char '\''))
     ; return(Syntax(Parsex(tag,OLD,arityCs,[(name,map fst arityCs)]))) }

newStylePx arityCs =
  do { symbol "syntax"
     ; tag <- parens(many (lower <|> char '\''))
     ; exts <- many casesPx
     ; return(Syntax(Parsex(tag,NEW,arityCs,exts)))
     }
     
casesPx =  
  do { name <- conName 
     ; args <- parens(sepBy1 conName (symbol ","))
     ; return(name,args)}


--------------------------------------                 
constrdec =
 do{ pos <- getPosition
   ; exists <- forallP <|> (return [])
   ; c <- conName
   ; domain <- many simpletyp
   ; eqs <- possible (reserved "where" >> sepBy1 proposition (symbol ","))
   ; return (Constr (loc pos) exists (Global c) domain eqs)
   }

forallP =
 do { (reserved "forall") <|> (reserved "exists")
                          <|> (symbol "ex" >> fail "Quantifier 'ex' is not supported any more, please use 'exists'.")
    ; ns <- targs
    ; symbol "."
    ; return ns
    }

------------------------------------------------------------------------
-- Unit Tests
------------------------------------------------------------------------
testP p s =
  case parse2 (do { ans <- p; whiteSpace; return ans}) s of
   Left err -> Left("\n'"++s++"'"++" causes error\n  "++err)
   Right (exp,[]) -> Right exp
   Right (exp,cs) -> Left("\n"++s++"\n   leaves postfix: "++cs)
   
testQ p s =
  case parse2 (do { ans <- p; whiteSpace; return ans}) s of
   Left err -> putStrLn ("\n'"++s++"'"++" causes error\n  "++err)
   Right (exp,s) -> putStrLn (s++" is OK."++" trailing \n"++s)
   
testE = testP expr
testD = testP decl
testL = testP (many (literal lit2Exp extToExp))

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

d1 = testD testdata
d2 = testD "f = \\ n -> if n==0 then True else n * (fact (n-1))"
d4 = testD "test :: forall a b . a -> (a,b)"
d5 = testD "f x = do { y <- Just 3; return(y + x) }"
d7 = testD "data Var:: *0 ~> *0 ~> *0 where \n  Z:: Var (w,x) w\n  S:: Var w x -> Var (y,w) x"
d8 = testD "data Exp:: *0 ~> *0 ~> *0 ~> *0 ~> *0 where\n Const:: t -> Exp past now future t\n Run:: (forall n . Exp past now (n,future) (Cd n future t)) -> Exp past now future t"
d9 = testD
  ("data P1:: Set ~> *0 ~> *0 where\n"++
   "  Pvar1 :: Label a -> P1 Univ t\n"++
   "  Pnil1 :: P1 (Plus Univ (Empty `Cons)) [t]")
d10 = testD "Bind :: Lub i j k => M i a -> (a -> M j b) -> M k b"
d11 = testD "data L:: *0 where\n N :: L\n C :: Int -> L -> L\n   deriving List(i)"
d12 = testD $
       "data Nat :: *1 where\n"++
       "  Z :: Nat\n"++
       "  S :: Nat ~> Nat\n"++
       " deriving List(b)"
d13 = testD "data Natural:: level n . *n where   Zero :: Natural"


p3 = testP program "id :: forall (k:: *1) (a:: *) . a -> a\nid x = x"
p4 = testP program "v (f,_) = V f\nv r = Lam r e self"
p5 = testP program ("le:: Nat ~> Boolean\n"++
                     "{le Z (S n)} = T")

e1 = testE "do { y <- tim; x <- poly ; x }"
e2 = testE "do { y <- Just 3; return(y + x) }"
e3 = testE "let {(u,v) = f x;(a,b) = g v } in u"
b1 = testE "[| \\ x -> x |]"
b2 = testE "[| \\ x -> x + 1 |]"
b3 = testE "\\ f -> [| \\ y -> f y |]"
b4 = testE "\\ f -> [| \\ y -> $f y |]"
b5 = testE "\\ f -> [| \\ y -> \\ z -> $f y |]"
b6 = testE "\\ f -> [| \\y -> $( (\\w -> [| $f $w |])   ( [| y + 1|] )) |]"
b7 = testE "\\ f -> [| \\y -> $( (\\z -> [| \\ q -> $f $z |])   ( [| y |] )) |]"
b8 = testE "let f x = \\ e -> if x==0 then e else [| let n = x in $(f (x-1) [| n + $e |]) |] in f 2"

b9 = testE " {\"a\"=3,\"b\"=5}l "
b10 = testE "\\ r -> { \"a\" =4; r}l "
b11 = testE " { `a=5, `b=True}a "
b12 = testE "( #3, 4n, \\ x -> (2+x)n )"
b13 = testE "3.4 #+ 4.5"

d14 = testD "g {a=x; r}l = (a,x,r)"
d15 = testD "(C \"a\" x r) = (\"z\",x,r)"
d16 = testD "f [x; r]i = (x,r)"

ls = testL " #\"abc\"  \"tim\" 'x' `d 123.4"
ls2 = parse2 (many (extP expr))
        " 123 #123 123n [x,y] [x,y;z] [a,b]l [a,b; c]l "

dectests = mapM ok [d1,d2,d4,d5,d7,d8,d9,d10,d11,d12,d13,d14,d15,d16]
progtests = mapM ok [p3,p4,p5]
exptests = mapM ok [e1,e2,e3,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13]
littests = mapM ok [ls]

tests = dectests >> progtests >> exptests >> littests

ok (Right x) = putStrLn "ok"
ok (Left s) = putStrLn s

tr :: String -> IO ()
tr s = case getExp s of
         Just e -> do { y <- freshE e; x <- (swp y); putStr(show x) }
         Nothing -> error ("Parsing error for: "++s)


----------------------------------------------------


Right(Program xxx) = unsafePerformIO(parseFile program "D:/work/sheard/research/omega/work.prg")

--(TypeSig lc v t) = xxx !! 0
--(FX _ _ ff tbs tfs) = vars [] t emptyF

ty2 = "app:: Seq a ~> Seq a ~> Seq a\n"++
      "{app Snil ys} = ys\n"++
      "{app (Scons x xs) ys} = Scons x {app xs ys}"

d6 = "data Natural:: level n . *n where\n"++
     "   Zero :: Natural\n"++
     "   Succ :: Natural ~> Natural\n" ++
     " deriving Nat(p)\n"
     
d45 = "data Natural':: level n . (Natural::*1) ~> *(n+1) where\n" ++
     "   Zero' :: Natural' Zero\n" ++
     "   Succ' :: Natural' n -> Natural' (Succ n)\n" ++
     " deriving Nat(s)"
