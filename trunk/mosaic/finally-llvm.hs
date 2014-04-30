{-# LANGUAGE DataKinds #-}

module FinallyLLVM where

class LLVM repr where
  cnst :: Int -> repr
  add :: repr -> repr -> repr
  -- (:=) :: repr -> repr -> repr


-- TEST

t1 :: LLVM repr => Maybe repr
t1 = do
  let i1 = add (cnst 2) (cnst 40)
  return i1
