{-# LANGUAGE TemplateHaskell, ViewPatterns, KindSignatures, DataKinds, RankNTypes, GADTs, ScopedTypeVariables, FlexibleInstances, StandaloneDeriving #-}
{-# LANGUAGE DatatypeContexts #-}

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Control.Applicative -- for ghc 7.8

-- GOAL: transform (simple) TH datatype splices to the format of level-aware inhabitants


ex = [d| data Foo = A | B (Foo :: *) deriving Show |]
ex0 = [d| data Foo a |]
ex' = [d| data Foo (a :: Bool) = A | B a (Foo :: *) |]
ex'' = [d| data (Show (a :: Bool), a ~ True) => Foo a = A | B a (Foo a) |] -- this needs DatatypeContexts

pex = runQ ex >>= print
pex0 = runQ ex0 >>= print
pex' = runQ ex' >>= print
pex'' = runQ ex'' >>= print


mex = map (toMy []) <$> runQ ex >>= print

data Nat = Z | S Nat

-- TODO: connect this to LC

class Levelled repr where
  star :: repr (S (S l))
  --inh :: repr (S l) -> (repr l -> repr l) -> repr l
  inh :: repr (S l) -> (repr l -> V repr) -> repr l
  --inhs :: repr (S l) -> (Vec n (repr l) -> V repr) -> repr l -- should be

instance Levelled repr -- FOR NOW!

data V :: (Nat -> *) -> * where
  V :: repr l -> V repr

--deriving
instance Show (V repr)

toMy :: Levelled repr => [(Name, V repr)] -> Dec -> V repr --- FOR NOW!
toMy [] (DataD [] nam [] [] _) = V (star `inh` V)
toMy env (DataD [] nam tvs [] _) = V (star `inh` (\i -> inner env tvs))
    where inner :: [(Name, V repr)] -> [TyVarBndr] -> V repr
          inner env [] = undefined
          inner env (PlainTV tvnam:tvs) = undefined

-- TODO: tyvars should be "outer" and constructors should be "inner"
