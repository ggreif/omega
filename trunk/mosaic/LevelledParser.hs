{-# LANGUAGE DataKinds, KindSignatures, GADTs, TupleSections, ViewPatterns #-}

import Control.Applicative
import Control.Monad

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


newtype CharParse (stratum :: Nat) a = CP (String -> Maybe (a, String))

instance P CharParse where
  star = CP $ \s -> do ('*' : rest) <- return s -- \do ('*' : rest)
                       return ((), rest)
  reserved w = CP $ \s -> do guard $ and $ zipWith (==) w s
                             return ((), drop (length w) s)

instance Monad (CharParse stratum) where
  return a = CP $ return . (a,)
  (CP f) >>= c = CP $ \s -> do (a, rest) <- f s -- do (f -> Just (a, rest)) <- return s -- \do f -> (a, rest)
                               runCP (c a) rest

runCP (CP f) = f
