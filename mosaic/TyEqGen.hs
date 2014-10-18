{-# LANGUAGE FlexibleInstances, GADTs, MultiParamTypeClasses, TypeOperators, TypeSynonymInstances, ViewPatterns #-}

module Data.Type.Equality.Generics where

import Data.Type.Equality
import GHC.Generics
import Unsafe.Coerce (unsafeCoerce)

sameRep :: (Generic a, Generic b) => Rep a x -> Rep b x -> Maybe (a :~: b)
sameRep = undefined


nameAndMod :: Datatype d => D1 d f a -> (String, String)
nameAndMod d = (datatypeName d, moduleName d)

sameDatatype :: (Datatype d, Datatype d') => D1 d f a -> D1 d' f' a' -> Maybe (d :~: d')
sameDatatype (nameAndMod -> l) (nameAndMod -> r) | l == r = Just $ unsafeCoerce Refl
sameDatatype _ _ = Nothing

class SameStructure f f' where
  sameStructure :: f a -> f' a -> Maybe (f :~: f')

instance (SameStructure f f', SameStructure g g') => SameStructure (f :+: g) (f' :+: g') where
  
instance (Constructor c, Constructor c') => SameStructure (C1 c f) (C1 c' f') where
  sameStructure l r = do Refl <- sameConstructor l r; return Refl


sameConstructor :: (Constructor c, Constructor c') => C1 c f a -> C1 c' f' a' -> Maybe (C1 c f a :~: C1 c' f' a')
sameConstructor (conName -> l) (conName -> r) | l == r = Just $ unsafeCoerce Refl
sameConstructor _ _ = Nothing

{-
data (:+:) (f :: * -> *) (g :: * -> *) p = L1 (f p) | R1 (g p)


-}