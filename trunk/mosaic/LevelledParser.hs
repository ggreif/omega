{-# LANGUAGE DataKinds, KindSignatures, GADTs, TupleSections, ViewPatterns
           , FlexibleContexts #-}

import Control.Applicative
import Control.Monad
import Data.Char

data Nat = Z | S Nat -- >    data Nat :: level l . *l where Z :: Nat; S :: Nat ~> Nat

data Nat' :: Nat -> * where
  Z' :: Nat' Z
  S' :: Nat' n -> Nat' (S n)

{-
data Nat' :: level l . Nat -> *(1+l) where
  Z' :: Nat' Z
  S' :: Nat' n -> Nat' (S n)
  data Foo :: Nat' x
    Bar :: Foo

Bar :: Foo _::_ Nat' x :: *1

       Bar :: Foo _::_ Nat' x :: *2
-}

class KnownStratum (stratum :: Nat)

instance KnownStratum Z
instance KnownStratum n => KnownStratum (S n)


class P (parser :: Nat -> * -> *) where
  star :: KnownStratum s => parser s ()
  reserved :: String -> parser s ()
  operator :: String -> parser s ()
  identifier :: parser s String
  constructor :: parser s String
  ascend :: parser (S s) a -> parser s a
  descend :: parser s a -> parser (S s) a

signature :: (P parser, KnownStratum s, Alternative (parser s)) => parser s ()
signature = star <|> star -- (star >> operator "~>" >> star)

dataDefinition :: (P parser, KnownStratum (S s), Monad (parser (S s)), Alternative (parser s), Alternative (parser ('S s))) => parser (S s) (String, (), [String])
dataDefinition = do reserved "data"
                    name <- constructor
                    operator "::"
                    sig <- signature
                    reserved "where"
                    inhabitants <- descend $ many inhabitant
                    return (name, sig, inhabitants)
    where inhabitant = constructor -- do c <- constructor; operator "::"; return c


newtype CharParse (stratum :: Nat) a = CP (String -> Maybe (a, String))

instance P CharParse where
  star = CP $ \s -> do ('*' : rest) <- return s -- \do ('*' : rest)
                       return ((), rest)
  reserved w = CP $ \s -> do guard $ and $ zipWith (==) w s
                             return ((), drop (length w) s)

  identifier = CP $ \s -> do (lead : rest) <- return s
                             guard $ isLower lead
                             let (more, rest') = span (liftA2 (||) isLower isUpper) rest
                             return $ (lead : more, rest')

  constructor = CP $ \s -> do (lead : rest) <- return s
                              guard $ isUpper lead
                              let (more, rest') = span (liftA2 (||) isLower isUpper) rest
                              return $ (lead : more, rest')

instance Monad (CharParse stratum) where
  return a = CP $ return . (a,)
  (CP f) >>= c = CP $ \s -> do (a, rest) <- f s -- do (f -> Just (a, rest)) <- return s -- \do f -> (a, rest)
                               runCP (c a) rest

runCP (CP f) = f
