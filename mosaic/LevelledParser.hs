{-# LANGUAGE DataKinds, KindSignatures, GADTs, TupleSections, ViewPatterns
           , FlexibleContexts, InstanceSigs, ScopedTypeVariables
           , TypeOperators, ConstraintKinds, PolyKinds, RankNTypes #-}

import Control.Applicative
import Control.Monad
import Data.Char
import GHC.Exts
import Data.Type.Equality

data Nat = Z | S Nat -- >    data Nat :: level l . *l where Z :: Nat; S :: Nat ~> Nat

data Nat' :: Nat -> * where
  Z' :: Nat' Z
  S' :: Nat' n -> Nat' (S n)

sameNat :: Nat' a -> Nat' b -> Maybe (a :~: b)
Z' `sameNat` Z' = Just Refl

{-
data Nat' :: level l . Nat -> *(1+l) where
  Z' :: Nat' Z
  S' :: Nat' n -> Nat' (S n)
  data Foo :: Nat' x
    Bar :: Foo

Bar :: Foo _::_ Nat' x :: *1

       Bar :: Foo _::_ Nat' x :: *2
-}

data Dict :: (k -> Constraint) -> k -> * where
  Dict :: c k => Dict c k

data AMDict :: (* -> *) -> * where
  AMDict :: (Alternative t, Monad t) => AMDict t

class KnownStratum (stratum :: Nat) where
  stratum :: Nat' stratum
  canDescend :: Nat' stratum -> Nat' below -> Maybe (stratum :~: S below, Dict KnownStratum below)

instance KnownStratum Z where stratum = Z'; canDescend _ _ = Nothing
instance KnownStratum n => KnownStratum (S n) where
  stratum = S' stratum
  canDescend (S' s) b | Just Refl <- s `sameNat` b = Just (Refl, Dict)
  canDescend _ _ = Nothing

class P (parser :: Nat -> * -> *) where
  star :: KnownStratum s => parser s ()
  reserved :: String -> parser s ()
  operator :: String -> parser s ()
  identifier :: parser s String
  constructor :: parser s String
  ascend :: parser (S s) a -> parser s a
  descend :: parser s a -> parser (S s) a

typeExpr :: (P parser, KnownStratum s, Alternative (parser s), Monad (parser s)) => parser s (Typ s)
typeExpr = (star >> return Star) -- <|> star -- (star >> operator "~>" >> star)

dataDefinition :: forall parser s . (P parser, KnownStratum (S s)) => (forall strat . AMDict (parser strat)) -> parser (S s) (DefData (S s))
dataDefinition d
           = case (d :: AMDict (parser (S s)), d :: AMDict (parser s)) of
               (AMDict, AMDict) ->
                 do reserved "data"
                    name <- constructor
                    operator "::"
                    typ <- typeExpr
                    reserved "where"
                    let inhabitant = let str = (stratum :: Nat' (S s)) in
                                       case str of
                                         S' b@(S' (_ :: Nat' s')) -> case canDescend str b of
                                           Nothing -> Left <$> constructor
                                           Just (Refl, Dict) -> Right <$> dataDefinition d
                                         _ -> Left <$> constructor
                    inhabitants <- descend $ many inhabitant
                    return $ DefData (Signature name typ) inhabitants

data Typ (stratum :: Nat) where
  Star :: KnownStratum stratum => Typ stratum
  --Star :: KnownStratum stratum => Typ (S (S stratum))

data Signature (stratum :: Nat) where
  Signature :: String -> Typ (S stratum) -> Signature stratum

data DefData (stratum :: Nat) where
  DefData :: Signature stratum -> [String `Either` DefData stratum] -> DefData (S stratum)


newtype CharParse (stratum :: Nat) a = CP (String -> Maybe (a, String))

parseLevel :: Nat' s -> CharParse s ()
parseLevel (S' (S' l)) = reserved $ show $ lev l
   where lev :: Nat' n -> Int
         lev Z' = 0
         lev (S' l) = 1 + lev l

instance P CharParse where
  star :: forall s . KnownStratum s => CharParse s ()
  star = CP $ \s -> do ('*' : rest) <- return s -- \do ('*' : rest)
                       runCP (parseLevel (stratum :: Nat' s)) rest

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

instance Functor (CharParse stratum) where
  fmap f (CP p) = CP $ fmap (\(a, str) -> (f a, str)) . p

instance Applicative (CharParse stratum) where
  pure = return
  (<*>) = ap

instance Monad (CharParse stratum) where
  return a = CP $ return . (a,)
  (CP f) >>= c = CP $ \s -> do (a, rest) <- f s -- do (f -> Just (a, rest)) <- return s -- \do f -> (a, rest)
                               runCP (c a) rest

runCP (CP f) = f
