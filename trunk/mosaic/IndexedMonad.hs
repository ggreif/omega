{-# LANGUAGE RebindableSyntax, PolyKinds, DataKinds, KindSignatures
           , GADTs, StandaloneDeriving, FlexibleInstances, FlexibleContexts
             #-}

module IndexedMonad where

import Prelude (Show(..), error, undefined, (==), ($))
import Data.Char
import Data.Maybe
import Data.Thrist

-- All my data has coordinates

data Nat = Z | S Nat
data Nat' :: Nat -> * where
  Z' :: Nat' Z
  S' :: Nat' n -> Nat' (S n)

deriving instance Show (Nat' n)

data Ch :: Nat -> Nat -> * where
  Ch :: Char -> Ch n (S n)

deriving instance Show (Ch m n)

(|.) = Cons
infixr 5 |.

substrate :: Thrist Ch Z (S(S(S(S Z))))
substrate = Ch 'a' |. Ch 'b' |. Ch 'c' |. Ch 'd' |. Nil

deriving instance Show (Thrist Ch st end)

data Parser dat st end where
   P :: (Nat' st -> Thrist Ch st end -> Maybe (dat st cool, Nat' cool, Thrist Ch cool end)) -> Parser dat st end

(>>=) :: Parser dat st end -> (dat st point -> Parser dat' st end) -> Parser dat' st end
_ >>= _ = undefined

return :: dat st point -> Parser dat st end
return = undefined

fail = error

char :: Char -> Nat' st -> Thrist Ch st end -> Maybe (Ch st (S st), Nat' (S st), Thrist Ch (S st) end)
char c n (Ch c' `Cons` rest) | c == c' = Just (Ch c', S' n, rest)
char _ _ (_ `Cons` rest) = Nothing

ca = P $ char 'a'
caa = do Ch a <- ca
         Ch a <- ca
         return undefined

data Split :: (Nat -> Nat -> *) -> Nat -> Nat -> * where
  Split :: dat st point -> Nat' point -> Thrist Ch point end -> Split dat st end

--deriving instance Show (Split dat st end)


run :: Nat' st -> Parser dat st end -> Thrist Ch st end -> Maybe (Split dat st end)
run st (P f) thr = case f st thr of
                  Just (got, n, rest) -> Just $ Split got n rest
                  Nothing -> Nothing

t0 = run Z' ca substrate