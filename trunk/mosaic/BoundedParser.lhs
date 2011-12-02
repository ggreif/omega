My objective is to implement a parser that reflect the
locations of the parsed stuff in the type of the stuff.

See my blog post: http://heisenbug.blogspot.com/2011/11/pondering-about-foundations.html

> module BoundedParser where
> import Text.Parsec
> import Data.Thrist
> import TypeMachinery (Z, S, Nat'(..))

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
>                return $ Bounded t undefined undefined

