We want to build parsers by parsing a file.
Each definition will create a new mini-parser
(respecting scope) that knows the identifiers
originating from below, whether they are injected
into the surrounding scope, etc.

This means we get (better?) error messages from
the parser about unrecognized identifiers.

------ example ------
data Foo = Zoom | Ra Int

data Bar :: level n . Bar ~> *n where
  Quux :: Bar Quux
  Baz :: Bar n ~> Bar (Baz n)
------ end ------

> {-# LANGUAGE RecursiveDo #-}

> import Text.Parsec

> data Decl = Decl

> symbol s = string s

> circ :: Parsec String () (Parsec String () Decl)
> circ = mdo symbol "data"
>            name <- symbol "Foo"
>            return undefined

