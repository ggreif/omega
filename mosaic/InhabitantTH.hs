module InhabitantTH where

import Inhabitants
import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax (runQ)

dataRewrite :: DecsQ -> DecsQ
dataRewrite q = do decs <- q
                   return $ map go decs
  where go :: Dec -> Dec
        go (DataD ctxt name tyvs cons derivs) = error $ show tyvs
        go a = error $ show a

