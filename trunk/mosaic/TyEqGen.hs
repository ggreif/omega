{-# LANGUAGE KindSignatures, TypeOperators, ViewPatterns #-}

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

{-
class Datatype d where
  datatypeName :: t d f a -> [Char]
  moduleName :: t d f a -> [Char]
-}