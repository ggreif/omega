{-# LANGUAGE DataKinds, KindSignatures, MultiParamTypeClasses
           , FlexibleInstances, GADTs, DeriveFunctor, StandaloneDeriving #-}

module FinallyLLVM where

import GHC.TypeLits
import Control.Applicative
import Control.Monad (ap)


data LLType = Void | Int | Label Symbol | Nat `X` LLType

class LLVM (repr :: LLType -> *) where
  cnst :: Int -> repr 'Int
  add :: repr ty -> repr ty -> repr ty
  -- (:=) :: repr -> repr -> repr
  phi :: repr ty -> repr (Label sym) -> repr ty

class (LLVM repr, Monad m) => Block m (repr :: LLType -> *) where
  instr :: repr ty -> m (repr ty)
  bind :: m (repr ty') -> (repr ty' -> m (repr ty)) -> m (repr ty)

--instance (LLVM repr, Monad m) => Monad (Block m repr)

-- TEST

-- a free-monad like thingy to implement Block
data TB a where
  Ret :: a -> TB a
  Bind :: TB ty' -> (ty' -> TB ty) -> TB ty

deriving instance Functor TB

instance Monad TB where
  return = Ret
  (>>=) = Bind

instance Applicative TB where
  pure = return
  (<*>) = ap

instance LLVM repr => Block TB repr where
  instr = return
  bind = (>>=)

t1 :: (LLVM repr) => TB (repr 'Int)
t1 = do
  let i1 = add (cnst 2) (cnst 40)
  return i1


--instance LLVM 