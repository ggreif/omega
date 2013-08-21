> {-# LANGUAGE GADTs, KindSignatures, StandaloneDeriving, ExistentialQuantification,
>              FlexibleInstances, TypeFamilies, UndecidableInstances #-}

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

> match :: P m n -> ExP m -> Maybe (Division m n)
> match Eo e@(ExP (l, Nil)) = Just $ Exact (Nil, e)
> match Eo _ = Nothing
> match p@(Ch c) (ExP (l, Cons (Ch c') rest)) | c == c' = Just $ Exact (Cons (Ch c') Nil, ExP (l, rest))
> match p@(Sq fst snd) inp = do pre <- match fst inp
>                               case pre of
>                                Exact (t, rest) -> do post <- match snd rest
>                                                      return $ combine pre post
>                                Fuzzy (t, n, rest) -> do post <- match snd rest
>                                                         return $ combine pre post
>   where combine (Exact (t, _)) (Exact (t', rest')) = Exact (appendThrist t t', rest')
>   --      matchSnd (Exact (_, r)) = match snd r
>   --      matchSnd (Fuzzy (_, r)) = match snd r

> {- match p@(Or l r) inp = case match l inp of
>                        Just (t1, rest1) -> Just (got1, p, rest1)
>                        Nothing -> case match r inp of
>                                   Just (got2, r, rest2) -> Just (got2, p, rest2)
>                                   Nothing -> Nothing -}

> class NatLike a where
>   type Simplify a

> instance NatLike Z where
>   type Simplify Z = Z
> instance NatLike n => NatLike (S n) where
>   type Simplify (S n) = (S n)
> instance (NatLike m, NatLike n) => NatLike (Or m n) where
>   type Simplify (Or m n) = RightAssocOr (Or m n)
>   --type Simplify (Or (Or m n) n') = Simplify (Or m (Or n n'))

Let's think of the cases of sequential composition
Assume we already start at a fuzzy position (Or m n)
and want to consume a fixed amount of k characters.

Or m n    +  (S (S (S Z)))  =  (S (S (S (Or m n))))  ==> simplifies to ==>  Or (S (S (S m))) (S (S (S n)))

When we want to consume a fuzzy number of chars, we double the branches

Or m n + Or r s = (m + r) `Or` (m + s) `Or` (n + r) `Or` (n + s)

(here we assume the variables are flat naturals)

> type family RightAssocOr a
> type instance RightAssocOr (Or (S m) n) = (Or (S m) n)

> data Division m n
>    = Exact (Thrist P m n, ExP n)
>    | forall n' . Fuzzy (Thrist P m n', Nat' n', ExP n')

> tZ = thristize Z

> tp1 = Ch 'P' `Sq` Ch 'G'
> t1 = match tp1 $ tZ "PG"
> t1a = match (tp1 `Sq` Eo) $ tZ "PG"
> t1b = match (tp1 `Sq` Eo) $ tZ "PGa"
