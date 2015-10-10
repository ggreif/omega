{-# LANGUAGE TemplateHaskell, ViewPatterns #-}

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

-- GOAL: transform (simple) TH splices to the format defined in ../def-use.hs

oneLamBinder :: Exp -> Exp
oneLamBinder (LamE [] e) = e -- FIXME: visit e
oneLamBinder lam@(LamE [p] e) = lam -- FIXME: visit e
oneLamBinder (LamE (p:ps) e) = LamE [p] (oneLamBinder (LamE ps e))


example = runQ (oneLamBinder <$> [|\a b -> a|]) >>= print

e1 = (toMy [] <$> [|\a b -> a b|]) :: Q Easy

class Lam repr where
  lam :: (repr -> repr) -> repr
  app :: repr -> repr -> repr


toMy :: Lam repr => [(Name, repr)] -> Exp -> repr
toMy env (VarE (flip lookup env -> Just v)) = v
toMy env (AppE f a) = app (toMy env f) (toMy env a)
toMy env (LamE [] e) = toMy env e
toMy env (LamE [VarP nam] e) = lam $ \v -> toMy ((nam, v) : env) e
toMy env (LamE (p:ps) e) = toMy env (LamE [p] $ LamE ps e)


data Easy = It | App Easy Easy | Lam (Easy -> Easy)

instance Lam Easy where
  lam = Lam
  app = App

instance Show Easy where
  show It = "It"
  show (App f a) = "(" ++ show f ++ " " ++ show a ++ ")"
  show (Lam f) = "(\\" ++ show It ++ " -> " ++ show (f It) ++ ")"