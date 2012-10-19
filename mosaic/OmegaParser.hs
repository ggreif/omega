module OmegaParser where

import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote

ω = QuasiQuoter { quoteExp = parseExprExp {-, quotePat = parseExprPat-} }


parseExprExp :: String -> TH.Q TH.Exp
parseExprExp "" = undefined
parseExprExp "s * h" = TH.varE $ TH.mkName "µ"

--parseExprPat :: String -> Q Pat
--parseExprPat ...
