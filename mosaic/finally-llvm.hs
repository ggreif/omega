{-# LANGUAGE DataKinds, KindSignatures #-}

module FinallyLLVM where

import GHC.TypeLits


data LLType = Int | Label Symbol | Nat `X` LLType

class LLVM (repr :: LLType -> *) where
  cnst :: Int -> repr 'Int
  add :: repr ty -> repr ty -> repr ty
  -- (:=) :: repr -> repr -> repr
  phi :: repr ty -> repr (Label sym) -> repr ty


-- TEST

t1 :: LLVM repr => Maybe (repr 'Int)
t1 = do
  let i1 = add (cnst 2) (cnst 40)
  return i1


--instance LLVM 