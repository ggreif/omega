{-# LANGUAGE KindSignatures, GADTs #-}

module InhabitantTH where

import Inhabitants
import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Lib
--import Language.Haskell.TH.Syntax (runQ)


class Inhabitable ent => Postulatable ent where
  postulate :: ent o (S' l) -> ent False l -- should be HOAS (like inhabit)

dataRewrite :: DecsQ -> DecsQ
dataRewrite q = do decs <- q
                   return $ map go decs
  where go :: Dec -> Dec
        go (DataD ctxt name tyvs cons derivs) = let posts :: [(Name, Nameable False (S' Z'))]; posts = map postulateTvs tyvs in error $ "tvs: " ++ concatMap (show . fst) posts
        go a = error $ show a

        postulateTvs :: Postulatable ent => TyVarBndr -> (Name, ent False (S' Z'))
        postulateTvs (PlainTV name) = (name, postulate starN)
        postulateTvs (KindedTV name StarT) = (name, postulate starN)
        postulateTvs (KindedTV name kind) = error $ "Needs reify? " ++ show kind


data Nameable (open :: Bool) (lev :: Nat') where
  Tyvar :: Nameable o (S' l) -> Name -> Nameable False l
  Anon :: (Name -> Nameable o l) -> Nameable o l


instance Inhabitable (Nameable) where
instance Postulatable (Nameable) where
  postulate = Anon . Tyvar
