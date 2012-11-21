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

> {-# LANGUAGE GADTs, KindSignatures, PolyKinds, DataKinds #-}

> module Parser where
> import Data.Thrist
> import Kinds.TypeMachinery

For now we try to ignore the fact that IParser should
be an IMonad (and IFunctor, IApplicable, IAlternative as well).


> data At :: * -> Nat -> Nat -> * where
>   HoldChar :: Char -> At Char n (St n)

> data IParser :: (Nat -> Nat -> *) -> Nat -> Nat -> * where
>   Char :: Char -> IParser a k (St k)


-- counting Char Thrist

> type One = St Zt
> type Two = St One
> type Three = St Two
> type Four = St Three
> type Five = St Four
> type Six = St Five
> type Seven = St Six

> infixr 5 -+
> l -+ t = Cons (HoldChar l) t

> t2 :: Thrist (At Char) Zt Six
> t2 = 'H' -+ 'e' -+ 'l' -+ 'l' -+ 'o' -+ '!' -+ Nil
