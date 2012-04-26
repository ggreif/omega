> {-# LANGUAGE GADTs, KindSignatures, StandaloneDeriving, ExistentialQuantification, FlexibleInstances #-}

> import TypeMachinery (Z, S, Nat'(..))
> import Data.Thrist

> data Or m n

> data P :: * -> * -> * where
>   Ch :: !Char -> P n (S n)
>   Or :: P m n -> P m n' -> P m (Or n n')
>   Sq :: P m n -> P n o -> P m o
>   Eo :: P e e

> deriving instance Show (P m n)

As a warm-up exercise we convert a String to a Thrist P consisting of Chs only

> data ExP m = forall n . ExP (Nat' n, Thrist P m n)
> deriving instance Show (ExP m)
> deriving instance Show (Thrist P m n)

> thristize :: Nat' m -> String -> ExP m
> thristize m [] = ExP (m, Nil)
> thristize m (c:cs) | ExP (l, t) <- thristize (S m) cs = ExP (l, Cons (Ch c) t)

Match a Ch Thrist by a more complex structure
TODO!

> match :: P m n -> String -> Maybe (String, Thrist P m n, String)
> match Eo "" = Just ("", Nil, "")
> match Eo rest = Nothing
> {- match p@(Ch c) (c':rest) | c == c' = Just ([c], p, rest)
> match p@(Sq fst snd) inp = do (got1, p', rest) <- match fst inp
>                               (got2, p'', rest') <- match snd rest
>                               return (got1 ++ got2, p, rest')
> match p@(Or l r) inp = case match l inp of
>                        Just (got1, l, rest1) -> Just (got1, p, rest1)
>                        Nothing -> case match r inp of
>                                   Just (got2, r, rest2) -> Just (got2, p, rest2)
>                                   Nothing -> Nothing
> -}

> tp1 = Ch 'P' `Sq` Ch 'G'
> t1 = match tp1 "PG"
> t1a = match (tp1 `Sq` Eo) "PG"
> t1b = match (tp1 `Sq` Eo) "PGa"
