{-# LANGUAGE FlexibleInstances #-}

module PrimParser ( charLiteral, intLiteral, stringLiteral
                  , identifierV, parens
                  , parserPairs, runParser ) where

import ParserAll
import Encoding
import Syntax(V(..),Var(..),Lit(..),Inj(..))
import Monads(FIO(..),Exception(..))
import System.IO.Unsafe(unsafePerformIO)
import Value(pv,analyzeWith)
import SyntaxExt(SynExt(..))

---------------------------------------------------------------
-- Encoding the datatypes necessary to implement Parsers

instance Encoding a => Encoding (Parser a) where
   to p = Vparser (p >>= return . to)
   from (Vparser p) = p >>= return . from
   from v = error ("Value not a Parser: "++(show v))

instance (Encoding a,Encoding b) => Encoding (a -> Parser b) where
    to f = Vprimfun "->" (return . to . f . from)
    from f = from . help . getf f . to
      where help :: FIO V -> V
            help (FIO w) = case unsafePerformIO w of
                           Ok (v@(Vlazy _ _)) -> help(analyzeWith return v)
                           Ok v -> v
                           Fail loc _ _ mess -> error("Near "++show loc++"\n"++mess)
            getf (Vprimfun _ f) = f
            getf (Vf f _ _) = f
            getf v = error ("Value not a function: "++(show v))


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

satisfyV = lift1 "satisfy" f where
  f v = return(Vparser(do { c <- satisfy g; return(Vlit(Char c)) }))
        where g u = from (backwards v (to u))


-- Lexeme oriented parsers that eat trailing white space

intLiteral = fmap fromInteger natural
identifierV = Vparser(fmap toStr identifier)

choiceD = lift2 "<!>" f where
  f (Vparser x) vf = return(Vparser(
     case backwards vf (Vlit Unit) of
       (Vparser y) -> x <|> y
       v -> error ("Not parsing value: "++show v)))

parse2P = lift2 "parse2" f where
  f (Vparser p) (VChrSeq cs)  =
     case parse2 p cs of
      Left message -> return(Vsum L (toStr message))
      Right(v,rest) -> return(Vsum R (Vprod v (VChrSeq rest)))
  f x y = fail ("bad inputs to parse2: "++show x++" and "++ pv y)

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
  [--("satisfy",satisfyV),
  --,("identifier",identifierV),("symbol",symbolV)
  --,("<!>",choiceD)
  ("parse2",parse2P)
  --,("buildExpressionParser",buildExpressionParserP)
  ,("toChrSeq",toChrSeqV),("fromChrSeq",fromChrSeqV)
  ]
