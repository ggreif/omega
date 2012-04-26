> {-# LANGUAGE GADTs, KindSignatures, StandaloneDeriving #-}

> import TypeMachinery (Z, S)
> import Data.Thrist

> data Or m n

> data P :: * -> * -> * where
>   Ch :: Char -> P n (S n)
>   Or :: P m n -> P m n' -> P m (Or n n')
>   Sq :: P m n -> P n o -> P m o
>   Eo :: P e e

> deriving instance Show (P m n)

> match :: P m n -> String -> Maybe (String, P m n, String)
> match Eo "" = Just ("", Eo, "")
> match Eo rest = Nothing
> match p@(Ch c) (c':rest) | c == c' = Just ([c], p, rest)
> match p@(Sq fst snd) inp = do (got1, p', rest) <- match fst inp
>                               (got2, p'', rest') <- match snd rest
>                               return (got1 ++ got2, p, rest')
> match p@(Or l r) inp = case match l inp of
>                        Just (got1, l, rest1) -> Just (got1, p, rest1)
>                        Nothing -> case match r inp of
>                                   Just (got2, r, rest2) -> Just (got2, p, rest2)
>                                   Nothing -> Nothing

> tp1 = Ch 'P' `Sq` Ch 'G'
> t1 = match tp1 "PG"
> t1a = match (tp1 `Sq` Eo) "PG"
> t1b = match (tp1 `Sq` Eo) "PGa"
