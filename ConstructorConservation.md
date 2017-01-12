# Example #

``` haskell
data Peano = Z | S Peano

plus Z n = n
plus (S m) n = plus m (S n) -- tail recursive
```
alternatively
``` haskell
plus Z = id
plus (S m) = plus m . S
```
using _view patterns_
``` haskell
{-# LANGUAGE ViewPatterns #-}
plus Z = id
plus (S (plus -> fn)) = fn . S
```

# Introduction #

When looking at all equality proofs dealing with `Nat`s there is a common principle: each line mentions the same number of `S` and `Z` in the patterns as on the RHS.

I call this _conservation of constructors_.

Is there any literature on it?

Comment from [Daniel Gorín](http://www8.cs.fau.de/~gorin): Does not work when we have two types of the interval, e.g. `S, T :: Nat -> Nat`. (GGR: This is for equality. Might work for other equivalence relations though.)

Is it okay to have one constructor in each dimension? (`Z`, `S`, `Homotopy`, etc.) --> Globular model.

Such a constraint surely restricts the number of candidates for a proof-search algorithm.

# Property Conservation #

The above principle is a pretty strong one, we may desire to forget some (exact) constructors, but count _depth_. I.e. for tree-like data we may be interested in the conservation of the _fringe_, or the _contour_ (fringe with depth of each element). For sorting we may want conservation of the _permutation_.

# Counting Proofs #

This might just be a special case of [counting proofs](http://www.cs.toronto.edu/~azadeh/resources/papers/popl14-counter.pdf).
