-- Time-stamp: <2010-06-15 10:56:02 cklin>

module Front where

import Types
import Data.Char
import Data.List
import System.IO

%{
Terminal = LexOp   as "+"
         | LexDef  as "="
         | LexArr  as "->"
         | LexComa as ","
         | LexSemi as ";"
         | LexLam  as "\\"
         | LexType as "::"
         | LexParL as "(" | LexParR as ")"
         | LexBraL as "{" | LexBraR as "}"
         | LexVar {Ident}
         | LexCon {String}
         | LexInt {Integer}
         | LexData | LexWhere
         | LexCase | LexOf
         | LexLet  | LexIn
         | LexNext
         | LexDoc {String}
         | LexError ;

top     {[Program]} ;
top     {[]}                        : ;
        {p}                         | LexNext, top {p} ;
        {d:p}                       | decl {d}, LexNext, top {p} ;

decl    {Program} ;
decl    {Value v (foldr Lam t ax)}  : LexVar {v}, vars {ax}, "=", term {t} ;
        {Decl (Data c ax) cx}       | LexData, LexCon {c}, vars {ax},
                                      conb {cx} ;
        {Info doc}                  | docs {doc} ;

docs    {[String]} ;
docs    {[c]}                       : LexDoc {c} ;
        {c:cx}                      | LexDoc {c}, docs {cx} ;

vars    {[Ident]} ;
vars    {[]}                        : ;
        {v:ax}                      | LexVar {v}, vars {ax} ;

conb    {[Cons]} ;
conb    {[]}                        : ;
        {cx}                        | LexWhere, "{", cons {cx}, "}" ;

cons    {[Cons]} ;
cons    {[Cons c t]}                : LexCon {c}, "::", tsig {t} ;
        {Cons c t:cx}               | LexCon {c}, "::", tsig {t}, ";",
                                      cons {cx} ;

tsig    {Type} ;
tsig    {t}                         : ftsig {t} ;
        {arrType t u}               | ftsig {t}, "->", tsig {u} ;

ftsig   {Type} ;
ftsig   {TyCon c ax}                : LexCon {c}, stsig {ax} ;
        {t}                         | atsig {t} ;

stsig   {[Type]} ;
stsig   {[t]}                       : atsig {t} ;
        {t:tx}                      | atsig {t}, stsig {tx} ;

atsig   {Type} ;
atsig   {TyVar v}                   : LexVar {v} ;
        {TyCon c []}                | LexCon {c} ;
        {TyCon "()" []}             | "(", ")" ;
        {TyCon "," [u, v]}          | "(", tsig {u}, ",", tsig {v}, ")" ;
        {t}                         | "(", tsig {t}, ")" ;

term    {Term} ;
term    {t}                         : sterm {t} ;
        {App (App (Var "+") t) u}   | sterm {t}, "+", term {u} ;
        {Lam a u}                   | "\\", LexVar {a}, "->", term {u} ;
        {Case c bx}                 | LexCase, term {c}, LexOf,
                                      "{", cases {bx}, "}" ;
        {Let dx t}                  | LexLet, "{", defs {dx}, "}",
                                      LexIn, term {t} ;

sterm   {Term} ;
sterm   {t}                         : aterm {t} ;
        {App t u}                   | sterm {t}, aterm {u} ;

aterm   {Term} ;
aterm   {Var v}                     : LexVar {v} ;
        {Con c}                     | LexCon {c} ;
        {Int i}                     | LexInt {i} ;
        {Con "()"}                  | "(", ")" ;
        {t}                         | "(", term {t}, ")" ;
        {App (App (Con ",") u) v}   | "(", term {u}, ",", term {v}, ")" ;

defs    {[(Ident, Term)]} ;
defs    {[(v, foldr Lam t ax)]}     : LexVar {v}, vars {ax}, "=", term {t} ;
        {(v, foldr Lam t ax):dx}    | LexVar {v}, vars {ax}, "=", term {t},
                                      ";", defs {dx} ;

cases   {[(Pat, Term)]} ;
cases   {[(p, t)]}                  : pat {p}, "->", term {t} ;
        {(p, t):cx}                 | pat {p}, "->", term {t},
                                      ";", cases {cx} ;

pat     {Pat} ;
pat     {PatCon c px}               : LexCon {c}, vars {px} ;
        {PatCon "," [u, v]}         | "(", LexVar {u}, ",", LexVar {v}, ")" ;
        {PatInt i}                  | LexInt {i} ;
}%

frown remain = fail (show (take 10 remain))

--------- Parse programs in files

parseFile :: String -> IO [Program]
parseFile file =
    do program <- readFile file
       top (segment program)

--------- Lexical analysis: top-level function

skiplf :: String -> String
skiplf = dropWhile ('\n' /=)

copydoc :: String -> ([String], String)
copydoc ('\n':cs@('-':'-':_)) = (doc:docs, rest)
    where (doc, wt) = span ('\n' /=) cs
          (docs, rest) = copydoc wt
copydoc cs = ([], cs)

segment :: String -> [Terminal]
segment [] = [LexNext]
segment ('\n':cs@('\n':'-':'-':_)) =
    let (doc, wt) = copydoc cs
    in LexNext : (map LexDoc doc ++ segment wt)
segment ('-':'-':cs) = segment (skiplf cs)
segment ('\n':'>':cs) = LexNext : segment (skiplf cs)
segment ('\n':'\n':'>':cs) = LexNext : segment (skiplf cs)
segment ('\n':cs@('\n':_)) = LexNext : segment cs
segment (c:cs) | isSpace c = segment cs
segment input =
    let (word, wt) = span isIdentChar input
        (symbol, st) = span isSymChar input
    in if null word
       then lexSymbol symbol ++ segment st
       else lexIdent word : segment wt

--------- Lexical analysis: symbols and operators

isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c == '_'

isSymChar :: Char -> Bool
isSymChar c = not (isIdentChar c || isSpace c)

keysyms0 :: [(Char, Terminal)]
keysyms0 = [(';',  LexSemi), (',',  LexComa),
            ('\\', LexLam),
            ('(',  LexParL), (')',  LexParR),
            ('{',  LexBraL), ('}',  LexBraR)]

-- Note that here I use the same token, LexOp, to represent three
-- different integer binary operators.  This is hack, but as long as we
-- only type (but not evaluate) the programs, there really is no need to
-- distinguish the operators, which all have the same type.

keysyms :: [(String, Terminal)]
keysyms = [("+",  LexOp),  ("=",  LexDef),
           ("*",  LexOp),  ("/",  LexOp),
           ("->", LexArr), ("::", LexType)]

lexSymbol :: String -> [Terminal]
lexSymbol [] = []
lexSymbol symbol@(s:sx) =
    case lookup s keysyms0 of
      Just token -> token:lexSymbol sx
      Nothing -> case lookup symbol keysyms of
                   Just token -> [token]
                   Nothing -> [LexError]

--------- Lexical analysis: keywords and identifiers

keywords :: [(String, Terminal)]
keywords = [("data", LexData), ("where", LexWhere),
            ("case", LexCase), ("of",    LexOf),
            ("let",  LexLet),  ("in",    LexIn)]

lexIdent :: String -> Terminal
lexIdent word =
    if all isDigit word then LexInt (read word)
    else if isUpper (head word) then LexCon word
         else if isLower (head word) then
                  case lookup word keywords of
                    Just token -> token
                    Nothing -> LexVar word
              else LexError

