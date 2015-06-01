{-# LANGUAGE DataKinds, KindSignatures, GADTs, TupleSections, ViewPatterns
           , FlexibleContexts, InstanceSigs, ScopedTypeVariables
           , TypeOperators, ConstraintKinds, PolyKinds, RankNTypes
           , StandaloneDeriving #-}

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
  failure :: parser s a

typeExpr :: forall parser s . (P parser, KnownStratum s, Alternative (parser s), Monad (parser s)) => parser s (Typ s)
typeExpr = starType <|> arrowType
  where starType = do star
                      S' (S' _) <- return (stratum :: Nat' s)
                      return Star
        arrowType = do dom <- starType
                       operator "~>"
                       cod <- typeExpr
                       return $ dom `Arr` cod

signature :: forall parser s . (P parser, KnownStratum s, Alternative (parser s), Alternative (parser (S s)), Monad (parser s), Monad (parser (S s))) => parser s (Signature s)
signature = do name <- constructor
               operator "::"
               typ <- ascend typeExpr
               return $ Signature name typ

dataDefinition :: forall parser s . (P parser, KnownStratum (S s)) => (forall strat . AMDict (parser strat)) -> parser (S s) (DefData (S s))
dataDefinition d
           = case (d :: AMDict (parser (S (S s))), d :: AMDict (parser (S s)), d :: AMDict (parser s)) of
               (AMDict, AMDict, AMDict) ->
                 do reserved "data"
                    --name <- constructor
                    --operator "::"
                    --typ@Star <- typeExpr; error $ show typ
                    sig <- signature
                    reserved "where"
                    let inhabitant = let str = (stratum :: Nat' (S s)) in
                                       case str of
                                         S' b@(S' (_ :: Nat' s')) -> case canDescend str b of
                                           Nothing -> Left <$> constructor
                                           Just (Refl, Dict) -> Right <$> dataDefinition d
                                         _ -> Left <$> constructor
                    inhabitants <- descend $ many inhabitant
                    return $ DefData undefined{-(Signature name typ)-} inhabitants

data Typ (stratum :: Nat) where
  Star :: KnownStratum (S (S stratum)) => Typ (S (S stratum))
  Arr :: Typ stratum -> Typ stratum -> Typ stratum

deriving instance Show (Typ stratum)

data Signature (stratum :: Nat) where
  Signature :: String -> Typ (S stratum) -> Signature stratum

deriving instance Show (Signature stratum)

data DefData (stratum :: Nat) where
  DefData :: Signature stratum -> [String `Either` DefData stratum] -> DefData (S stratum)

deriving instance Show (DefData stratum)

newtype CharParse (stratum :: Nat) a = CP (String -> Maybe (a, String))

parseLevel :: Nat' s -> CharParse s ()
parseLevel (S' (S' l)) = reserved $ show $ lev l -- FIXME
   where lev :: Nat' n -> Int
         lev Z' = 0
         lev (S' l) = 1 + lev l
parseLevel _ = failure

instance P CharParse where
  star :: forall s . KnownStratum s => CharParse s ()
  star = CP $ \s -> do ('*' : rest) <- return s -- \do ('*' : rest)
                       runCP (parseLevel (stratum :: Nat' s)) rest

  reserved w = CP $ \s -> do guard $ and $ zipWith (==) w s
                             guard . not . null $ drop (length w - 1) s
                             return ((), drop (length w) s)

  operator o = CP $ \s -> do guard $ and $ zipWith (==) o s
                             guard . not . null $ drop (length o - 1) s
                             return ((), drop (length o) s)

  identifier = CP $ \s -> do (lead : rest) <- return s
                             guard $ isLower lead
                             let (more, rest') = span (liftA2 (||) isLower isUpper) rest
                             return $ (lead : more, rest')

  constructor = CP $ \s -> do (lead : rest) <- return s
                              guard $ isUpper lead
                              let (more, rest') = span (liftA2 (||) isLower isUpper) rest
                              return $ (lead : more, rest')

  failure = CP $ const Nothing
  ascend (CP f) = CP f
  descend (CP f) = CP f


instance Functor (CharParse stratum) where
  fmap f (CP p) = CP $ fmap (\(a, str) -> (f a, str)) . p

instance Applicative (CharParse stratum) where
  pure = return
  (<*>) = ap

instance Alternative (CharParse stratum) where
  empty = failure
  CP l <|> CP r = CP $ \s -> case (l s, r s) of
                              (l, Nothing) -> l
                              (l@(Just (_, lrest)), Just (_, rrest)) | length lrest <= length rrest -> l
                              (_, r) -> r

instance Monad (CharParse stratum) where
  return a = CP $ return . (a,)
  (CP f) >>= c = CP $ \s -> do (a, rest) <- f s -- do (f -> Just (a, rest)) <- return s -- \do f -> (a, rest)
                               runCP (c a) rest

runCP (CP f) = f
