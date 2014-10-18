{-# LANGUAGE FlexibleInstances, GADTs, MultiParamTypeClasses, TypeOperators, TypeSynonymInstances, ViewPatterns #-}

module Data.Type.Equality.Generics where

import Data.Type.Equality
import GHC.Generics
import Unsafe.Coerce (unsafeCoerce)

--sameRep :: (Generic a, Generic b) => Rep a x -> Rep b x -> Maybe (a :~: b)

sameRep :: (Datatype d, Datatype d', SameStructure f f') => D1 d f a -> D1 d' f' a -> Maybe (D1 d f :~: D1 d' f')
--sameRep = undefined
sameRep l@(M1 l') r@(M1 r') = do Refl <- sameDatatype l r
	      	        	 Refl <- sameStructure l' r'
				 return Refl


nameAndMod :: Datatype d => D1 d f a -> (String, String)
nameAndMod d = (datatypeName d, moduleName d)

sameDatatype :: (Datatype d, Datatype d') => D1 d f a -> D1 d' f' a' -> Maybe (d :~: d')
sameDatatype (nameAndMod -> l) (nameAndMod -> r) | l == r = Just $ unsafeCoerce Refl
sameDatatype _ _ = Nothing

class SameStructure f f' where
  sameStructure :: f a -> f' a -> Maybe (f :~: f')

both :: (f :+: g) a -> (f a, g a)
both = const (undefined, undefined)

instance (SameStructure f f', SameStructure g g') => SameStructure (f :+: g) (f' :+: g') where
  sameStructure (both -> (x, y)) (both -> (x', y')) = do Refl <- x `sameStructure` x'
  		      	     	       	       	      	 Refl <- y `sameStructure` y'
							 return Refl

instance (Constructor c, Constructor c') => SameStructure (C1 c f) (C1 c' f') where
  sameStructure l r = do Refl <- sameConstructor l r; return Refl


sameConstructor :: (Constructor c, Constructor c') => C1 c f a -> C1 c' f' a' -> Maybe (C1 c f a :~: C1 c' f' a')
sameConstructor (conName -> l) (conName -> r) | l == r = Just $ unsafeCoerce Refl
sameConstructor _ _ = Nothing

{-
data (:+:) (f :: * -> *) (g :: * -> *) p = L1 (f p) | R1 (g p)


-}