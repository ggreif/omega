{-# LANGUAGE GADTs, StandaloneDeriving, KindSignatures, DeriveFunctor, ViewPatterns, PatternSynonyms #-}
module OmegaParser where

import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax (runQ)
import Text.Parsec
--import Text.Parsec.Token
import Text.Parsec.String
import Control.Applicative

ω = QuasiQuoter { quoteExp = parseExprExp }

-- Omega AST

data Exp :: * -> * where
  Var :: String -> Exp a
  Con :: String -> Exp a
  App :: Exp (a -> b) -> Exp a -> Exp b
  IntLit :: Int -> Exp Int

--deriving instance Functor Exp

--instance Applicative Exp where
lexeme :: Parser a -> Parser a
lexeme p = do { x <- p; spaces; return x }
integer = lexeme $ do { ds <- many1 digit; return $ IntLit (read ds) }

-- TH helpers
var = TH.varE . TH.mkName
con = TH.conE . TH.mkName
int = TH.litE . TH.IntegerL

trans :: Either a (Exp Int) -> TH.ExpQ
trans (Right (IntLit i)) = con "Int" `TH.appE` int (toInteger i)

parseExprExp :: String -> TH.Q TH.Exp
parseExprExp "" = fail "empty parse"
parseExprExp "s * h" = var "⊥"
parseExprExp s = do loc <- TH.location
                    let file = TH.loc_filename loc
                        exp = parse integer file s
                    trans exp

pattern a `Arr` b = TH.ArrowT `TH.AppT` a `TH.AppT` b
--pattern a `Deg` b = (TH.ConT (TH.Name (TH.OccName "°") (TH.NameQ (TH.ModName "Main")))) `TH.AppT` a `TH.AppT` b
pattern Deg name a b = TH.ConT name `TH.AppT` a `TH.AppT` b

refined :: DecsQ -> DecsQ
refined q = do decs <- q
               return $ map go decs
  where go :: TH.Dec -> TH.Dec
        go (TH.SigD name typ) = TH.SigD name (filterType typ)
        go a = a
        filterType (TH.ForallT univs ctx (filterType -> typ)) = TH.ForallT univs ctx typ
        filterType ((filterType -> a) `Arr` (filterType -> b)) = a `Arr` b
        filterType deg@(Deg (show -> "Main.°") a b) = b
        filterType app@(f `TH.AppT` a) = error $ show app
        filterType (error . show -> bla) = bla