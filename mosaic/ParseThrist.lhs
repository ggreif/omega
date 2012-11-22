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
>              StandaloneDeriving #-}

> module Parser where
> import Data.Thrist
> import Kinds.TypeMachinery

For now we try to ignore the fact that IParser should
be an IMonad (and IFunctor, IApplicable, IAlternative as well).


> data At :: * -> Nat -> Nat -> * where
>   HoldChar :: Char -> At Char n (St n)

> deriving instance Show (At t s e)

> data IParser :: (Nat -> Nat -> *) -> Nat -> Nat -> * where
>   --Char :: Char -> IParser a k (St k)
>   P :: (Nat' k -> Thrist p k (St k) -> (Maybe (p k (St k)), Thrist p (St k) (St k))) -> IParser p k (St k)


> char :: Char -> IParser (At Char) n (St n)
> char c = P check
>   where check k (Cons r@(HoldChar c') rest) | c == c' = (Just r, rest)

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

