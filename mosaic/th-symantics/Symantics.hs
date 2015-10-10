{-# LANGUAGE TemplateHaskell #-}

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

-- GOAL: transform (simple) TH splices to the format defined in ../def-use.hs

oneLamBinder :: Exp -> Exp
oneLamBinder (LamE [] e) = e -- FIXME: visit e
oneLamBinder lam@(LamE [p] e) = lam -- FIXME: visit e
oneLamBinder (LamE (p:ps) e) = LamE [p] (oneLamBinder (LamE ps e))


example = runQ (oneLamBinder <$> [|\a b -> a|]) >>= print