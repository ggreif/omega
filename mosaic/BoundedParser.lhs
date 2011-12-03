My objective is to implement a parser that reflect the
locations of the parsed stuff in the type of the stuff.

See my blog post: http://heisenbug.blogspot.com/2011/11/pondering-about-foundations.html

> {-# LANGUAGE GADTs, KindSignatures #-}

> module BoundedParser where
> import Text.Parsec
> import Data.Thrist
> import TypeMachinery (Z, S, Nat'(..), toNat')

Our tokens coming from the underlying parser are
outfitted with bounds. These become visible in the
type of the token.

Note: we do not yet require that e is strictly bigger than a.

> data BoundedToken t a e = Bounded t (Nat' a) (Nat' e)
>  deriving Show

We have to lift the parser operations into our bounded
world.

> bounded :: Monad m => ParsecT s u m t -> ParsecT s u m (BoundedToken t a e)
> bounded p = do a <- getPosition
>                t <- p
>                e <- getPosition
>                return $ Bounded t undefined undefined -- (toNat' $ sourceColumn a) (toNat' $ sourceColumn e)

We want to obtain a thrist as a result of parsing (see blog post)
and we describe our Parser as a thrist (see paper:
http://omega.googlecode.com/files/Thrist-draft-2011-11-20.pdf )

> data Parse :: * -> * -> * where
>  Atom :: Char -> Parse Char Char
>  Sure :: (a -> b) -> Parse a b
>  Try :: (a -> Maybe b) -> Parse a b
>  Or :: Parse a b -> Parse a b -> Parse a b
>  Rep1 :: Parse a b -> Parse [a] ([b], [a])
>  Rep :: Parse [a] (b, [a]) -> Parse [a] ([b], [a])
>  Group :: [Parse a b] -> Parse [a] ([b], [a])
>  Par :: Parse a b -> Parse c d -> Parse (a, c) (b, d)
>  Wrap :: Thrist Parse a b -> Parse a b

We need to translate Thrist Parse to Parsec, and the result
of running the parser should be a BoundedToken thrist.

> baz :: Stream s m a => Thrist Parse a b -> ParsecT s u m b
> baz (Cons (Atom c) Nil) = char c

Backup material
---------------

foldMThrist :: Monad m => (forall j k. (a +> j) -> (j ~> k) -> m (a +> k)) -> (a +> b) -> Thrist (~>) b c -> m (a +> c)