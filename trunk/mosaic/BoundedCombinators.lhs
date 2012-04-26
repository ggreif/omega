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

> match :: P m n -> ExP m -> Maybe (Thrist P m n, ExP n)
> match Eo e@(ExP (l, Nil)) = Just (Nil, e)
> match Eo _ = Nothing
> match p@(Ch c) (ExP (l, Cons (Ch c') rest)) | c == c' = Just (Cons (Ch c') Nil, ExP (l, rest))
> match p@(Sq fst snd) inp = do (t, rest) <- match fst inp
>                               (t', rest') <- match snd rest
>                               return (appendThrist t t', rest')
> {- match p@(Or l r) inp = case match l inp of
>                        Just (got1, l, rest1) -> Just (got1, p, rest1)
>                        Nothing -> case match r inp of
>                                   Just (got2, r, rest2) -> Just (got2, p, rest2)
>                                   Nothing -> Nothing
> -}

> tZ = thristize Z

> tp1 = Ch 'P' `Sq` Ch 'G'
> t1 = match tp1 $ tZ "PG"
> t1a = match (tp1 `Sq` Eo) $ tZ "PG"
> t1b = match (tp1 `Sq` Eo) $ tZ "PGa"
