{-# LANGUAGE TemplateHaskell, ViewPatterns, KindSignatures, DataKinds, RankNTypes, GADTs, ScopedTypeVariables, FlexibleInstances #-}

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

-- GOAL: transform (simple) TH splices to the format defined in ../def-use.hs

oneLamBinder :: Exp -> Exp
oneLamBinder (LamE [] e) = e -- FIXME: visit e
oneLamBinder lam@(LamE [p] e) = lam -- FIXME: visit e
oneLamBinder (LamE (p:ps) e) = LamE [p] (oneLamBinder (LamE ps e))


example = runQ (oneLamBinder <$> [|\a -> a|]) >>= print

e1 = (toMy [] <$> [|\a b -> b a|]) :: Q (E Easy Root)

data Lo = Root | Lef Lo | Rig Lo -- | Abs Loc

class Lam (repr :: Lo -> Lo -> *) where
  --lam :: ((forall u' . repr (Lef u) u') -> repr d' (Rig u)) -> repr u u
  lam :: ((forall u' . Known u' => repr (Lef u) u') -> E repr (Rig u)) -> repr u u
  app :: repr u' (Lef u) -> repr u'' (Rig u) -> repr u u
  --defless :: repr d' u -> repr d u


class Known (loc :: Lo)

instance Known Root
instance Known loc => Known (Lef loc)
instance Known loc => Known (Rig loc)

data V (repr :: Lo -> Lo -> *) where
  V :: (forall u' . Known u' => repr (Lef u) u') -> V repr

data E (repr :: Lo -> Lo -> *) (use :: Lo) where
  E :: Known u => repr d u -> E repr u

instance Show (E Easy u) where
  show (E e) = show e

toMy :: forall repr u . (Known u, Lam repr) => [(Name, V repr)] -> Exp -> E repr u
toMy env (VarE (flip lookup env -> Just (V v))) = E v
toMy env (AppE f a) = case (toMy env f, toMy env a) of (E f', E a') -> E (app f' a')
toMy env (LamE [] e) = toMy env e
toMy env (LamE [VarP nam] e) = E (lam (\v -> toMy ((nam, V v) : env) e))
   --where f :: (forall u' . repr (Lef u) u') -> E repr (Rig u)
   --      f v = toMy ((nam, V v) : env) e
   --      --f v = case toMy ((nam, V v) : env) e of E e' -> defless e'
toMy env (LamE (p:ps) e) = toMy env (LamE [p] $ LamE ps e)

instance Lam Easy where
  lam = Lam
  app = App
  --defless = Some

data Easy :: Lo -> Lo -> * where
  It :: Easy (Lef u) u'
  App :: Easy u' (Lef u) -> Easy u'' (Rig u) -> Easy u u
  Lam :: ((forall u' . Easy (Lef u) u') -> E Easy (Rig u)) -> Easy u u
  --Some :: Easy d' u -> Easy d u


instance Show (Easy d u) where
  show It = "It"
  show (App f a) = "(" ++ show f ++ " " ++ show a ++ ")"
  show (Lam f) = "(\\" ++ show It ++ " -> " ++ show (f It) ++ ")"
  --show (Some e) = show e