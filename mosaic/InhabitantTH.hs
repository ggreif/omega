module InhabitantTH where

import Inhabitants ()
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax (runQ)

dataRewrite :: DecsQ -> DecsQ
dataRewrite q = do decs <- q
                   return $ map go decs
  where go :: TH.Dec -> TH.Dec
        go a = error $ show a

