{-# LANGUAGE DataKinds, KindSignatures, MultiParamTypeClasses #-}

module FinallyLLVM where

import GHC.TypeLits


data LLType = Int | Label Symbol | Nat `X` LLType

class LLVM (repr :: LLType -> *) where
  cnst :: Int -> repr 'Int
  add :: repr ty -> repr ty -> repr ty
  -- (:=) :: repr -> repr -> repr
  phi :: repr ty -> repr (Label sym) -> repr ty

class (LLVM repr, Monad m) => Block m (repr :: LLType -> *) where
  instr :: repr ty -> m (repr ty)
  bind :: repr ty' -> (repr ty' -> m (repr ty)) -> m (repr ty)

--instance (LLVM repr, Monad m) => Monad (Block m repr)

-- TEST


t1 :: (LLVM repr, Block m repr) => m (repr 'Int)
t1 = do
  let i1 = add (cnst 2) (cnst 40)
  return i1


--instance LLVM 