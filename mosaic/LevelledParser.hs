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
S' a `sameNat` S' b | Just Refl <- a `sameNat` b = Just Refl
_ `sameNat` _ = Nothing

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

-- Precedence climbing expression parser
--  http://eli.thegreenplace.net/2012/08/02/parsing-expressions-by-precedence-climbing

data Precedence = Parr | P1 | P2 | P3 | P4 | P5 | P6 | P7 | P8 | P9 | Papp deriving (Eq, Ord)
data Associativity = AssocNone | AssocLeft | AssocRight deriving (Eq, Ord)

go :: (CharParse ~ parser, Monad (parser s)) => parser s atom -> [((Precedence, Associativity), parser s atom -> parser s (atom -> atom))] -> [((Precedence, Associativity), parser s (atom -> atom))] -> parser s atom
go atom curr all = do a <- atom
                      let done = ((Parr, AssocRight), const $ return id)
                          choice = foldr1 (<|>)
                          parse (_, AssocRight) p = p atom <|> p (go atom curr all)
                          parse (_, AssocLeft) p = p atom <|>
                                       (do b <- p atom
                                           c <- choice $ map (uncurry parse) (done : curr)
                                           return $ const $ c (b a))
                      rests <- choice $ map (uncurry parse) (done : curr)
                      return $ rests a

expr1 = go (Named <$> constructor) [((Parr, AssocRight), \atomp -> do operator "~>"; b <- atomp; return (`Arr`b))] []

expr10 = go (Named <$> constructor) [((Papp, AssocLeft), \atomp -> do peek (Named <$> constructor); b <- atomp; return (`Arr`b))] []


-- NOTE: Later this will be just expression (which is stratum aware)
typeExpr :: forall parser s . (P parser, KnownStratum s, Alternative (parser s), Monad (parser s)) => parser s (Typ s)
typeExpr = starType <|> arrowType <|> simpleType
  where starType = do star
                      S' (S' _) <- return (stratum :: Nat' s)
                      return Star
        arrowType = do dom <- starType
                       operator "~>"
                       cod <- typeExpr
                       return $ dom `Arr` cod
        simpleType = do S' _ <- return (stratum :: Nat' s); Named <$> (constructor <|> identifier)

signature :: forall parser s . (P parser, KnownStratum s, Alternative (parser (S s)), Monad (parser s), Monad (parser (S s))) => parser s (Signature s)
signature = do name <- constructor
               operator "::"
               typ <- ascend typeExpr
               return $ Signature name typ

dataDefinition :: forall parser s . (P parser, KnownStratum s) => (forall strat . AMDict (parser strat)) -> parser (S s) (DefData (S s))
dataDefinition d
           = case (d :: AMDict (parser (S (S s))), d :: AMDict (parser (S s)), d :: AMDict (parser s)) of
               (AMDict, AMDict, AMDict) ->
                 do reserved "data"
                    sig <- signature
                    reserved "where"
                    let inhabitant = let str = (stratum :: Nat' s) in
                                       case str of
                                         (S' b) -> case canDescend str b of
                                           Nothing -> Left <$> signature
                                           Just (Refl, Dict) -> Right <$> dataDefinition d
                                         _ -> Left <$> signature
                    inhabitants <- descend $ many inhabitant
                    return $ DefData sig inhabitants

data Typ (stratum :: Nat) where
  Star :: KnownStratum (S (S stratum)) => Typ (S (S stratum))
  Arr :: Typ stratum -> Typ stratum -> Typ stratum
  Named :: String -> Typ (S stratum)

deriving instance Show (Typ stratum)

data Signature (stratum :: Nat) where
  Signature :: String -> Typ (S stratum) -> Signature stratum

deriving instance Show (Signature stratum)

data DefData (stratum :: Nat) where
  DefData :: Signature (S stratum) -> [Signature stratum `Either` DefData stratum] -> DefData (S stratum)

deriving instance Show (DefData stratum)

newtype CharParse (stratum :: Nat) a = CP (String -> Maybe (a, String))

parseLevel :: Nat' s -> CharParse s ()
parseLevel (S' (S' Z')) = reserved "0" <|> return () -- FIXME
parseLevel (S' (S' l)) = reserved $ show $ lev l -- FIXME
   where lev :: Nat' n -> Int
         lev Z' = 0
         lev (S' l) = 1 + lev l
parseLevel _ = failure

token :: CharParse s a -> CharParse s a
token p = id <$> p <* many space
  where space = CP $ \s -> do ((isSpace ->True) : rest) <- return s
                              return ((), rest)

cP = token . CP

peek :: CharParse s a -> CharParse s a
peek p = CP $ \s -> case runCP p s of Just (a, _) -> Just (a, s); _ -> Nothing

instance P CharParse where
  star :: forall s . KnownStratum s => CharParse s ()
  star = cP $ \s -> do ('*' : rest) <- return s -- \do ('*' : rest)
                       runCP (parseLevel (stratum :: Nat' s)) rest

  reserved w = cP $ \s -> do guard $ and $ zipWith (==) w s
                             guard . not . null $ drop (length w - 1) s -- TODO: peek not alnum
                             return ((), drop (length w) s)

  operator o = cP $ \s -> do guard $ and $ zipWith (==) o s
                             guard . not . null $ drop (length o - 1) s -- TODO: peek not symbol
                             return ((), drop (length o) s)

  identifier = cP $ \s -> do (lead : rest) <- return s
                             guard $ isLower lead
                             let (more, rest') = span (liftA2 (||) isLower isUpper) rest
                             return $ (lead : more, rest')

  constructor = cP $ \s -> do (lead : rest) <- return s
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
