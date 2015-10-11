{-# LANGUAGE TemplateHaskell, ViewPatterns, KindSignatures, DataKinds, RankNTypes, GADTs #-}

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

-- GOAL: transform (simple) TH splices to the format defined in ../def-use.hs

oneLamBinder :: Exp -> Exp
oneLamBinder (LamE [] e) = e -- FIXME: visit e
oneLamBinder lam@(LamE [p] e) = lam -- FIXME: visit e
oneLamBinder (LamE (p:ps) e) = LamE [p] (oneLamBinder (LamE ps e))


example = runQ (oneLamBinder <$> [|\a b -> a|]) >>= print

e1 = (toMy [] <$> [|\a b -> a b|]) :: Q (E Easy Root)

data Lo = Root | Lef Lo | Rig Lo -- | Abs Loc

class Lam (repr :: Lo -> Lo -> *) where
  lam :: (forall u' . repr (Lef u) u' -> repr d' (Rig u)) -> repr u u
  app :: repr u' (Lef u) -> repr u'' (Rig u) -> repr u u

data V (repr :: Lo -> Lo -> *) where
  V :: (forall u' . repr (Lef u) u') -> V repr

data E (repr :: Lo -> Lo -> *) (use :: Lo) where
  E :: repr d u -> E repr u

toMy :: Lam repr => [(Name, V repr)] -> Exp -> E repr u
toMy env (VarE (flip lookup env -> Just (V v))) = E v
toMy env (AppE f a) = case (toMy env f, toMy env a) of (E f', E a') -> E (app f' a')
   -- where E f' = toMy env f

{-
toMy :: Lam repr => [(Name, repr)] -> Exp -> repr
toMy env (VarE (flip lookup env -> Just v)) = v
toMy env (AppE f a) = app (toMy env f) (toMy env a)
toMy env (LamE [] e) = toMy env e
toMy env (LamE [VarP nam] e) = lam $ \v -> toMy ((nam, v) : env) e
toMy env (LamE (p:ps) e) = toMy env (LamE [p] $ LamE ps e)
-}

instance Lam Easy where
  lam = Lam
  app = App


data Easy :: Lo -> Lo -> * where
  It :: Easy (Lef u) u'
  App :: Easy u' (Lef u) -> Easy u'' (Rig u) -> Easy u u
  Lam :: (forall u' . Easy (Lef u) u' -> Easy d' (Rig u)) -> Easy u u


instance Show (Easy d u) where
  show It = "It"
  show (App f a) = "(" ++ show f ++ " " ++ show a ++ ")"
  show (Lam f) = "(\\" ++ show It ++ " -> " ++ show (f It) ++ ")"