# Introduction #

Imagine following type function:
```
tuple :: Nat ~> *
{tuple 0t} = ()
{tuple 1t} = a
{tuple (2+m)t} = (a, {tuple (1+m)t})
```

Now, let's see how this function can be used to parametrize a GADT:

```
data Tuple :: n ~> {tuple n} where
  Unit :: Tuple 0t
  Item :: Int -> Tuple 1t
  Pair :: Int -> Int -> Tuple 2t
```

# Details #

The type constructor's range must be `*n`.
Currently Ωmega enforces this directly, without performing a normalization step:

```
In the data declaration for 'Tuple' the range:
   {tuple n}
is not of the form *n, for some Level n.
```

# Open Questions #

  * does this construction work at all?
  * can this construction be used to implement parametrized modules?
  * ... type classes? _gasp!_ How can dictionary passing be emulated? Open type classes too?
  * how costly would it be to modify Ωmega to accept this construct? And GHC ? ;-)

# Crazier Still #

```
newtype Bar = Foo Int
```
Here `Foo` can be regarded as an _infinitesimal_ with an equation

Bar = Int + Foo

For `data` we need constrained variables (polynomials)
```
data Baz = A Int | B Bar
```

Baz = A `*` Int + B `*` Bar where A, B in {0, 1} and A + B == 1

Can we have a datatype algebra this way? Dependent types too?