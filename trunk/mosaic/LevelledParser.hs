{-# LANGUAGE DataKinds, KindSignatures, GADTs, TupleSections, ViewPatterns
           , FlexibleContexts, InstanceSigs, ScopedTypeVariables
           , TypeOperators, ConstraintKinds, PolyKinds, RankNTypes
           , StandaloneDeriving, TypeFamilies #-}

import Control.Applicative
import Control.Monad
import Data.Char
import GHC.Exts
import Data.Type.Equality
import Data.Map (Map)
import qualified Data.Map as Map

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
  type State parser
  peek :: parser s a -> parser s (a, State parser)
  accept :: State parser -> parser s ()

  star :: KnownStratum s => parser s ()
  reserved :: String -> parser s ()
  operator :: String -> parser s ()
  identifier :: parser s String
  constructor :: parser s String
  ascend :: parser (S s) a -> parser s a
  descend :: parser s a -> parser (S s) a
  failure :: parser s a
  token :: parser s a -> parser s a

-- Precedence climbing expression parser
--  http://eli.thegreenplace.net/2012/08/02/parsing-expressions-by-precedence-climbing

data Precedence = Parr | P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7 | P8 | P9 | Papp deriving (Eq, Ord)
data Associativity = AssocNone | AssocLeft | AssocRight deriving (Eq, Ord)

precedenceClimb :: (P parser, Alternative (parser s), Monad (parser s)) => parser s atom -> Map (Precedence, Associativity) (parser s atom -> parser s (atom -> atom)) -> parser s atom
precedenceClimb atom ops = go atom' ops'
  where atom' = atom <|> do operator "("; a <- go atom' ops'; operator ")"; return a -- FIXME
        ops' = Map.toList ops
        go atom curr = do let done = ((Parr, AssocNone), const $ return id)
                              munchRest = choice $ map (uncurry parse) (done : curr)
                              choice = foldr1 (<|>)
                              parse (_, AssocNone) p = p atom
                              parse (x, AssocRight) p = p atom <|> 
                                               do b <- p (go atom $ filter (\((y,_),_) -> y >= x) curr)
                                                  c <- munchRest
                                                  return $ \a -> c (b a)
                              parse (x, AssocLeft) p = p atom <|>
                                               do b <- p (go atom $ filter (\((y,_),_) -> y > x) curr)
                                                  c <- munchRest
                                                  return $ \a -> c (b a)
                          a <- atom
                          rests <- munchRest
                          return $ rests a

expr1 :: CharParse (S Z) (Typ (S Z))
expr1 = precedenceClimb (Named <$> constructor) $ Map.fromList [((Parr, AssocRight), \atomp -> do operator "~>"; b <- atomp; return (`Arr`b))]

expr10 :: CharParse (S Z) (Typ (S Z))
expr10 = precedenceClimb atom $ Map.fromList [((Papp, AssocLeft), \atomp -> do peek atomp; b <- atomp; return (`App`b))]
  where atom = Named <$> constructor

expr11 :: CharParse (S Z) (Typ (S Z))
expr11 = precedenceClimb atom $ Map.fromList
                 [ ((Parr, AssocRight), \atomp -> do operator "~>"; b <- atomp; return (`Arr`b))
                 , ((P8, AssocLeft), \atomp -> do operator "`"; i <- identifier; guard $ i /= "rrr"; operator "`"; b <- atomp; return (\a -> Named i `App` a `App` b))
                 , ((P9, AssocRight), \atomp -> do operator "`"; i <- identifier; guard $ i == "rrr"; operator "`"; b <- atomp; return (\a -> Named i `App` a `App` b))
                 , ((Papp, AssocLeft), \atomp -> do (b, state) <- peek atomp; accept state; return (`App`b))
                 ]
  where atom = Named <$> constructor

-- NOTE: we need to rule out mixed associativity operators with same precedence in one compound expression
--    see: http://stackoverflow.com/questions/15964064/left-associative-operators-vs-right-associative-operators



-- NOTE: Later this will be just expression (which is stratum aware)
typeExpr :: forall parser s ty . (Universe ty, P parser, KnownStratum s, Alternative (parser s), Monad (parser s)) => parser s (ty s)
typeExpr = precedenceClimb atom $ Map.fromList operators
  where atom = starType <|> namedType
        starType = do star; S' S'{} <- return (stratum :: Nat' s); return tStar
        namedType = do S'{} <- return (stratum :: Nat' s); tNamed <$> (constructor <|> identifier)
        operators = [ ((Parr, AssocRight), \atom -> do operator "~>"; b <- atom; S'{} <- return (stratum :: Nat' s); return (`tArr`b))
                    , ((P9, AssocLeft), \atom -> do operator "`"; i <- namedType; operator "`"; b <- atom; return (\a -> i `tApp` a `tApp` b))
                    , ((Papp, AssocLeft), \atom -> do (b, state) <- peek atom; accept state; return (`tApp`b))
                    ]

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
                    let inhabitant = case stratum :: Nat' s of
                                       str@(S' b) -> case canDescend str b of
                                         Nothing -> Left <$> signature
                                         Just (Refl, Dict) -> Right <$> dataDefinition d
                                       _ -> Left <$> signature
                    inhabitants <- descend $ many inhabitant
                    return $ DefData sig inhabitants

-- for now this is a *type* Universe, later it may represent all
-- expressions (values/types/kinds, etc.)
--
class Universe (ty :: Nat -> *) where
  tStar :: KnownStratum (S (S stratum)) => ty (S (S stratum))
  tArr :: ty (S stratum) -> ty (S stratum) -> ty (S stratum)
  tApp :: ty stratum -> ty stratum -> ty stratum
  tNamed :: String -> ty (S stratum)

instance Universe Typ where
  tStar = Star
  tArr = Arr
  tApp = App
  tNamed = Named

data Typ (stratum :: Nat) where
  Star :: KnownStratum (S (S stratum)) => Typ (S (S stratum))
  Arr :: Typ (S stratum) -> Typ (S stratum) -> Typ (S stratum)
  App :: Typ stratum -> Typ stratum -> Typ stratum
  Named :: String -> Typ (S stratum)

infixr 0 `Arr`
infixl 9 `App`

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

cP = token . CP

instance P CharParse where
  type State CharParse = String
  peek p = CP $ \s -> case runCP p s of Just a -> Just (a, s); _ -> Nothing
  accept = CP . const . return . ((),)

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
                             let (more, rest') = span isAlphaNum rest
                             return $ (lead : more, rest')

  constructor = cP $ \s -> do (lead : rest) <- return s
                              guard $ isUpper lead
                              let (more, rest') = span (liftA2 (||) isLower isUpper) rest
                              return $ (lead : more, rest')

  failure = CP $ const Nothing
  ascend (CP f) = CP f
  descend (CP f) = CP f
  token p = id <$> p <* many space
    where space = CP $ \s -> do ((isSpace -> True) : rest) <- return s
                                return ((), rest)


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

instance MonadPlus (CharParse stratum) where
  mzero = failure
  mplus = (<|>)

runCP (CP f) = f

runCP' :: proxy stratum -> CharParse stratum (c stratum) -> String -> Maybe ((c stratum), String)
runCP' _ (CP f) = f
