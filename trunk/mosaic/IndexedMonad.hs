{-# LANGUAGE NoImplicitPrelude, PolyKinds, DataKinds, KindSignatures, GADTs #-}

module IndexedMonad where

import Prelude (undefined, (==), ($))
import Data.Char
import Data.Maybe
import Data.Thrist

-- All my data has coordinates

data Nat = Z | S Nat
data Nat' :: Nat -> * where
  Z' :: Nat' Z
  S' :: Nat' n -> Nat' (S n)

data Ch :: Nat -> Nat -> * where
  Ch :: Char -> Ch n (S n)

(|.) = Cons
infixr 5 |.

substrate :: Thrist Ch Z (S(S(S(S Z))))
substrate = Ch 'a' |. Ch 'b' |. Ch 'c' |. Ch 'd' |. Nil


data Parser dat st end where
   P :: (Thrist Ch st end -> (Maybe (dat st cool), Thrist Ch cool end)) -> Parser dat st end


char :: Char -> Thrist Ch st end -> (Maybe (Ch st (S st)), Thrist Ch (S st) end)
char c (Ch c' `Cons` rest) | c == c' = (Just (Ch c'), rest)
--char _ (_ `Cons` rest) = (Nothing, rest)

ca = P $ char 'a'

data Split :: (Nat -> Nat -> *) -> Nat -> Nat -> * where
  Split :: dat st point -> Nat' point -> Thrist Ch point end -> Split dat st end

run :: Parser dat st end -> Thrist Ch st end -> Maybe (Split dat st end)
run (P f) thr = case f thr of
                  (Just got, rest) -> Just $ Split got undefined rest

