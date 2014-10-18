{-# LANGUAGE TypeOperators, ViewPatterns #-}

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


sameConstructor :: (Constructor c, Constructor c') => C1 c f a -> C1 c' f' a' -> Maybe (c :~: c')
sameConstructor (conName -> l) (conName -> r) | l == r = Just $ unsafeCoerce Refl
sameConstructor _ _ = Nothing

{-
class Constructor c where
  conName :: t c f a -> [Char]

-}