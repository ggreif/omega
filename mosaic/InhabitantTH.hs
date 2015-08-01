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
        go (DataD ctxt name tyvs cons derivs) = let posts = map postulateTvs tyvs in error $ "tvs: " ++ concatMap (show . (\(n, Anon f) -> f name)) posts
        go a = error $ show a

        postulateTvs :: Postulatable ent => TyVarBndr -> (Name, ent False (S' Z'))
        postulateTvs (PlainTV name) = (name, postulate starN)
        postulateTvs (KindedTV name StarT) = (name, postulate starN)
        postulateTvs (KindedTV name kind) = error $ "Needs reify? " ++ show kind


data Nameable (open :: Bool) (lev :: Nat') where
  Star :: Nameable True l
  Tyvar :: Nameable o (S' l) -> Name -> Nameable False l
  Anon :: (Name -> Nameable o l) -> Nameable o l

instance Show (Nameable o l) where
  show Star = "*"
  show (Anon f) = show $ f $ mkName "_"
  show (Tyvar isle name) = show name ++ " :: " ++ show isle

instance Inhabitable (Nameable) where
  starN = Star
instance Postulatable (Nameable) where
  postulate = Anon . Tyvar
