Okay, here is what I believe is at the heart of things:

   @[Char]@ is to @Parsec a@
as
   @Thrist (At Char)@ is to @IParser (At a)@

And we can compare the signatures now

runParsec :: Parsec a -> [Char] -> (Maybe a, [Char])

vs. (simplified)

runIParser :: IParser (At a) -> Thrist (At Char) -> (Maybe (At a), Thrist (At Char))

plus, we need to add the positional information

runIParser :: IParser (At a) (k, l) -> Thrist (At Char) (k, m) -> Maybe (At a (k, l), Thrist (At Char) (l, m))

> {-# LANGUAGE GADTs, KindSignatures, PolyKinds, DataKinds, FlexibleInstances,
>              StandaloneDeriving, TypeOperators, TypeHoles #-}

> {-# LANGUAGE RebindableSyntax #-}

> module Parser where
> import Data.Thrist
> import Kinds.TypeMachinery

For now we try to ignore the fact that IParser should
be an IMonad (and IFunctor, IApplicable, IAlternative as well).


> data At :: * -> Nat -> Nat -> * where
>   HoldChar :: Char -> At Char n (St n)
>   -- HoldString :: Nat' len -> String -> At Char n (Plus len n)
>   HoldChars :: Thrist (At Char) Zt len -> At Char n (Plus len n)

> deriving instance Show (At t s e)

> data IParser :: (Nat -> Nat -> *) -> Nat -> Nat -> * where
>   P :: (Nat' k -> Thrist p k (St k) -> (Maybe (p k (St k)), Thrist p (St k) (St k))) -> IParser p k (St k)


> char :: Char -> IParser (At Char) n (St n)
> char c = P check
>   where check k (Cons r@(HoldChar c') rest) | c == c' = (Just r, rest)


foldrThrist :: (forall i j. (i `arr` j) -> (j `brr` c) -> i `brr` c) -> (b `brr` c) -> Thrist arr a b -> a `brr` c

Commutativity:
Nat' len -> Nat' (len `Plus` Zt)

Hint: use the technique suggested in
http://stackoverflow.com/questions/13555547/how-can-i-get-the-length-of-dependently-typed-interval

> --shift :: Nat' by -> Nat' (len `Plus` Zt) -> Nat' (len `Plus` by)
> --shift Z n = n
> --shift (S m) n = shift m (S n)


> thristShift :: Nat' n -> Thrist p Zt len -> Thrist p n (len `Plus` n)
> thristShift n Nil = Nil
> --thristShift n (Cons e es) = Cons undefined (thristShift n es)


> --chars :: Thrist (At Char) Zt len -> IParser (At Char) n (Plus len n)
> --chars cs = P $ check cs
> --  where check :: Nat' len -> Thrist (At Char) a (Plus len a) -> Nat' n -> IParser (At Char) n (Plus len n)
> --        check len (Cons (HoldChar c) cs) k (Cons r@(HoldChar c') rest) | c == c' = undefined -- _ -- (Just _, rest)

> --move :: Nat' offs -> Thrist (At Char) here (Plus len here) -> Thrist (At Char) offs (Plus len offs)
> --move _ Nil = Nil
> --move (S Z) (Cons (HoldChar c) as) = Cons (HoldChar c) $ move (S (S Z)) as

> --thristLen :: Thrist (At Char) here (Plus len here) -> Nat' len
> --thristLen Nil = Z



> runIParser :: IParser p k (St k) -> Nat' k -> Thrist p k (St k) -> (Maybe (p k (St k)), Thrist p (St k) (St k))
> runIParser (P p) k t = p k t

-- counting Char Thrist

> type One = St Zt
> type Two = St One
> type Three = St Two
> type Four = St Three
> type Five = St Four
> type Six = St Five
> type Seven = St Six

> instance Show (Thrist (At Char) m n) where
>   show t = '"' : go t ('"':[])
>     where go :: Thrist (At Char) m' n' -> String -> String
>           go Nil acc = acc
>           go (Cons (HoldChar c) rest) acc = c : go rest acc

> infixr 5 -+
> l -+ t = Cons (HoldChar l) t

> t1 = runIParser (char 'H') Z ('H' -+ Nil)

> t2 :: Thrist (At Char) Zt Six
> t2 = 'H' -+ 'e' -+ 'l' -+ 'l' -+ 'o' -+ '!' -+ Nil

