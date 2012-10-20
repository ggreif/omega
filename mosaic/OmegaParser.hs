module OmegaParser where

import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Text.Parsec

ω = QuasiQuoter { quoteExp = parseExprExp {-, quotePat = parseExprPat-} }


parseExprExp :: String -> TH.Q TH.Exp
parseExprExp "" = fail "empty parse"
parseExprExp "s * h" = TH.conE $ TH.mkName "Δ"

--parseExprPat :: String -> Q Pat
--parseExprPat ...
