{-# LANGUAGE FlexibleInstances #-}
module PrimParser (intLitV,parserPairs,runParser) where

import ParserAll
import Encoding
import Syntax(V(..),Var(..),Lit(..),Inj(..))
import Monads(FIO(..),Exception(..))
import System.IO.Unsafe(unsafePerformIO)
import Value(pv,analyzeWith)
import SyntaxExt(SynExt(..))

intLit :: Parser Int
intLit = natural >>= (return . fromInteger)
charLit = charLiteral
stringLit = stringLiteral

---------------------------------------------------------------
-- Encoding the datatypes necessary to implement Parsers

instance Encoding a => Encoding (Parser a) where
   to p = Vparser (p >>= return . to)
   from (Vparser p) = p >>= return . from
   from v = error ("Value not a Parser: "++(show v))

instance (Encoding a,Encoding b) => Encoding (a -> Parser b) where
    to f = undefined -- Vprimfun "->" (return . to . f . from)
    --from (Vprimfun s f) = (fmap from) . f . to
    from v = error ("Value not a function: "++(show v))

{-
instance Encoding (Parser V) where
   to p = Vparser p
   from (Vparser p) = p
   from v = error ("Value not a Parser: "++(show v))

instance Encoding (Parser(V -> V)) where
   to p = Vparser (fmap (\ f -> lift1 "Parser(V->V)" (return.f)) p)
   from (Vparser p) = fmap backwards p
   from v = error ("Not a Parser: "++show v)
-}

backwards :: V -> (V -> V)
backwards fun v = help ((getf fun) v)
  where help (FIO w) =
             case unsafePerformIO w of
                Ok (v@(Vlazy _ _)) -> help(analyzeWith return v)
                Ok v -> v
                Fail loc _ _ mess -> error("Near "++show loc++"\n"++mess)
        getf (Vf f _ _) = f
        getf (Vprimfun _ f) = f
        getf v = error ("Not function in backwards: "++ show v)

{-
instance Encoding (Parser(V -> V -> V)) where
   to p = Vparser (fmap (\ f -> lift2 "Parser(V->V->V)" (\ a b ->return(f a b))) p)
   from (Vparser p) = fmap back2 p
     where back2 :: V -> (V -> V -> V)
           back2 v a b = backwards ((backwards v) a) b
   from v = error ("Not a Parser: "++show v)
-}

{-
instance Encoding (Operator V) where
   to (Infix p x) = Vcon (Global "Infix",Ox) [to p,to x]
   to (Prefix p) = Vcon (Global "Prefix",Ox) [to p]
   to (Postfix p) = Vcon (Global "Postfix",Ox) [to p]
   from (Vcon (Global "Infix",_) [p,x]) = Infix (from p) (from x)
   from (Vcon (Global "Prefix",_) [p]) = Prefix (from p)
   from (Vcon (Global "Postfix",_) [p]) = Postfix (from p)
   from v = error ("Not an Operator: "++(show v))
-}

instance Encoding Assoc where
   to AssocLeft  = Vcon (Global "AssocLeft",Ox)  []
   to AssocRight = Vcon (Global "AssocRight",Ox) []
   to AssocNone  = Vcon (Global "AssocNone",Ox)  []
   from (Vcon (Global "AssocLeft",_)  []) = AssocLeft
   from (Vcon (Global "AssocRight",_)  []) = AssocRight
   from (Vcon (Global "AssocNone",_)  []) = AssocNone
   from v = error ("Not an Assoc: "++show v)

------------------------------------------------------------
-- Parser Primitives

-- Char Oriented Parsers

charV = lift1 "char" f where
  f (Vlit(Char c)) = return(Vparser(char c >>= (return . Vlit . Char)))

satisfyV = lift1 "satisfy" f where
  f v = return(Vparser(do { c <- satisfy g; return(Vlit(Char c)) }))
        where g u = from (backwards v (to u))

stringV = lift1 "string" f where
  f v = return(Vparser(fmap to (string (from v))))

-- Lexeme oriented parsers that eat trailing white space

intLitV = Vparser(intLit >>= (return . Vlit . Int))
charLitV = Vparser(charLit >>= (return . Vlit . Char))
stringLitV = Vparser(stringLit >>= (return . toStr))
identifierV = Vparser(identifier >>= (return . toStr))
symbolV = lift1 "symbol" f where
  f v = return(Vparser(symbol (from v) >>= (return . toStr)))
choiceP = lift2 "<|>" f where
  f (Vparser x) (Vparser y) = return(Vparser( x <|> y))

choiceD = lift2 "<!>" f where
  f (Vparser x) vf = return(Vparser(
     case backwards vf (Vlit Unit) of
       (Vparser y) -> x <|> y
       v -> error ("Not parsing value: "++show v)))

manyP = lift1 "many" f where
  f (Vparser p) = return(Vparser(do { vs <- many p; return(consUp vs) }))
parensP = lift1 "parens" f where
  f (Vparser p) = return(Vparser(parens p))
tryP = lift1 "try" f where
  f (Vparser p) = return(Vparser(try p))
parse2P = lift2 "parse2" f where
  f (Vparser p) (VChrSeq cs)  =
     case parse2 p cs of
      Left message -> return(Vsum L (toStr message))
      Right(v,rest) -> return(Vsum R (Vprod v (VChrSeq rest)))
  f x y = fail ("bad inputs to parse2: "++show x++" and "++ pv y)


betweenP = lift3 "between" f where
  f (Vparser a) (Vparser b) (Vparser c) = return(Vparser(between a b c))

sepByP = lift2 "sepBy" f where
  f (Vparser a) (Vparser b) = return(Vparser(fmap to (sepBy a b)))


------------------------------------------------
-- Make Parser an monad

returnParserP = lift1 "returnParser" ret
  where ret v = return(Vparser(return v))

bindParserP = lift2 "bindParser" bind where
 bind (Vparser p) f = return(Vparser
  (do { v <- p
      ; let (FIO z) = case f of
                        Vf f _ _ -> f v
                        Vprimfun _ f -> f v
      ; case unsafePerformIO z of
          Ok(Vparser q) -> q
          Fail loc n k message -> fail ("\n\n**** Near "++show loc++"\n"++message)
      }))

failParserP = lift1 "failParser" f where
  f (VChrSeq s) = return(Vparser(fail s))

--------------------------------------------------------------
-- Make Expression Parsers
{-
buildExpressionParserP = lift2 "buildExpressionParser" f where
  f oper parser = return(Vparser(buildExpressionParser
                                  (from oper) (from parser)))
-}
----------------------------------------------------------------
-- ChrSeq to and from [Char]

toChrSeqV = lift1 "toChrSeq" f where
  f v = return(VChrSeq (from v))

fromChrSeqV = lift1 "toChrSeq" f where
  f (VChrSeq cs) = return(to cs)

---------------------------------------------------------------
-- Running a parser (simplistic, suppress error messages)

runParser :: Parser a -> String -> Maybe a
runParser p str = case parse p "<omega input>" str of
                  Left _ -> Nothing
                  Right y -> Just y

---------------------------------------------------------------
-- The list of pairs that is exported

parserPairs =
  [("char",charV),("satisfy",satisfyV),("string",stringV)
  ,("intLit",intLitV),("stringLit",stringLitV),("charLit",charLitV)
  ,("identifier",identifierV),("symbol",symbolV)
  ,("<|>",choiceP),("<!>",choiceD)
  ,("many",manyP),("parens",parensP),("try",tryP),("parse2",parse2P)
  ,("between",betweenP),("sepBy",sepByP)
  ,("returnParser",returnParserP),("bindParser",bindParserP)
  ,("failParser",failParserP)
  --,("buildExpressionParser",buildExpressionParserP)
  ,("toChrSeq",toChrSeqV),("fromChrSeq",fromChrSeqV)
  ]
