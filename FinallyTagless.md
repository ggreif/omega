# Introduction #

This is work of Carette et al.

[Oleg's tutorial](http://okmij.org/ftp/tagless-final/course/lecture.pdf) is very good

Consider these identities:
  * `type Empty = forall a . a`
  * `type Empty' = forall a . () => a`
  * `type Finally (c :: * -> Constraint) = forall a . c a => a; type Empty'' = Finally ()`
  * `data Empty'''` (no constructors)

To check the isomorphisms, we need to construct (round-trip) functions:

```
{-# LANGUAGE RankNTypes, LambdaCase, EmptyCase #-}
f2d :: Empty -> Empty'''
f2d a = a

d2f :: Empty''' -> Empty
d2f = \case {}
```


# Questions #

Can we encode structured graphs (esp. those which have PHOAS variables)?

# Tinkering #

Can I encode a multi-level lambda calculus in final tagless form?

Let's try! What is the grammar?

Term`<n>` ::= Star<2+n> | V`<n>` | App Term`<n>` Term`<n>` | Lam Term`<n>` | Annot Term`<n>` Term`<n+1>`

_There is only ever only one variable in this calculus :-)_

```hs

class LC (rep :: Nat -> *) where
star :: rep (2+n)
int :: rep (1+n)
arr :: rep (1+n) -> rep (1+n) -> rep (1+n)
cnst :: Int -> rep 1
var :: rep n
lam :: rep n -> rep n
app :: rep n -> rep n -> rep n
annot :: rep n -> rep (n+1) -> rep n
```

Of course these should be split up in TypeLC{annot}, BuiltinLC{cnst, int, star}
TypeLC should contain `typeof :: rep n -> rep (n+1)`.

## Constructing `data` types ##

The next complication is to construction of a user-defined data type with inhabitants
```
  dta :: String -> (rep (1+n), String -> rep n)
```

The first result is the new data type and the second a factory for the (nullary) inhabitants.