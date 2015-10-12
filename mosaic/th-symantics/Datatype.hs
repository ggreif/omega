{-# LANGUAGE TemplateHaskell, ViewPatterns, KindSignatures, DataKinds, RankNTypes, GADTs, ScopedTypeVariables, FlexibleInstances, StandaloneDeriving #-}

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

-- GOAL: transform (simple) TH datatype splices to the format of level-aware inhabitants


ex = [d| data Foo = A | B (Foo :: *) |]

pex = runQ ex >>= print


mex = map (toMy []) <$> runQ ex >>= print

data Nat = Z | S Nat

-- TODO: connect this to LC

class Levelled repr where
  star :: repr (S l)
  inh :: repr (S l) -> (repr l -> repr l) -> repr l

instance Levelled repr -- FOR NOW!

data V :: (Nat -> *) -> * where
  V :: repr l -> V repr

--deriving
instance Show (V repr)

toMy :: Levelled repr => [(Name, V repr)] -> Dec -> V repr --- FOR NOW!
toMy [] (DataD [] nam [] [] _) = V (star `inh` id)
