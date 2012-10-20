{-# LANGUAGE GADTs, StandaloneDeriving, KindSignatures, DeriveFunctor #-}
module OmegaParser where

import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Text.Parsec
--import Text.Parsec.Token
import Text.Parsec.String
import Control.Applicative

ω = QuasiQuoter { quoteExp = parseExprExp }

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


trans (Right (IntLit i)) = (TH.conE $ TH.mkName "Int") `TH.appE` (TH.litE $ TH.IntegerL (toInteger i))

parseExprExp :: String -> TH.Q TH.Exp
parseExprExp "" = fail "empty parse"
parseExprExp "s * h" = TH.conE $ TH.mkName "Δ"
parseExprExp s = do loc <- TH.location
                    let file = TH.loc_filename loc
                        exp = parse integer file s
                    trans exp
