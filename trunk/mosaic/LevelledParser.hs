{-# LANGUAGE DataKinds, KindSignatures, GADTs #-}

import Control.Applicative

data Nat = Z | S Nat

data Nat' :: Nat -> * where
  Z' :: Nat' Z
  S' :: Nat' n -> Nat' (S n)

class P (interp :: Nat -> * -> *) where
  star :: interp s ()
  reserved :: String -> interp s ()
  operator :: String -> interp s ()
  identifier :: interp s String
  constructor :: interp s String
  ascend :: interp (S s) a -> interp s a
  descend :: interp s a -> interp (S s) a

signature :: (P interp, Alternative (interp s)) => interp s ()
signature = star <|> star

dataDefinition :: (P interp, Monad (interp (S s)), Alternative (interp s), Alternative (interp ('S s))) => interp (S s) (String, (), [String])
dataDefinition = do reserved "data"
                    name <- constructor
                    operator "::"
                    sig <- signature
                    reserved "where"
                    alts <- descend $ many alt
                    return (name, sig, alts)
    where alt = constructor



