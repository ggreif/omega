# For the Sake of Aesthetics #

Here is a pretty picture, so you'll remember and come back :-)

![http://www.athropolis.com/arctic-facts/iceberg/iceberg-type.jpg](http://www.athropolis.com/arctic-facts/iceberg/iceberg-type.jpg)

(from www.athropolis.com)

For Hemingway's version, see http://en.wikipedia.org/wiki/Iceberg_Theory

# Introduction #

Usually programmers encounter data types as isolated or mutually recursive entities.

```
data Nat = Z | S Nat
data Foo = F Bar
data Bar = B Foo
```


# The Idea #

We argue that actually the different data types are just the _apparent_ parts of a big data type, just like there might be visible tips of a great iceberg.
```
data Iceberg :: Tag ~> * where
  Z :: Iceberg〈Nat〉
  S :: Iceberg〈Nat〉-> Iceberg〈Nat〉
  F :: Iceberg〈Bar〉-> Iceberg〈Foo〉
  B :: Iceberg〈Foo〉-> Iceberg〈Bar〉
```
This idea is an old one. Ahn & Sheard use it in their [paper](IcebergTypes#Mendler_Style_Recursion_Combinators.md) to model mutually recursive GADTs.

# Projections #

We can employ projections to get back our distinct surface types. We need two steps:
  1. partition the constructors by the `Iceberg〈TAG〉` in the result type.
  1. wrap each group with a `data` declaration, and drop all decorations.

# Open Questions #

## Parametrized Types? ##

Can we integrate parametrized types into the iceberg? Probably yes, if we allow `Iceberg :: Tag ~> τ`. Of course `τ` must be variant on the tag. Also, `τ` must be extracted to build the projections.

Since we wish to integrate n-ary types into the iceberg, `τ` must actually be of `∫ ~> *`, where `∫` can be a telescope (i.e. a dependent context). The telescopes for each tag must unify in length and componentwise, so we should possibly pair it up with the tag as in `〈TAG, ∫〉`.

## Levels? ##

How do other levels (kinds, sorts, etc.) fit in? As `Iceberg :: Lvl ~> Tag ~> τ`, possibly? What are the consistency conditions for this scheme? Can we model level polymorphism too?

### Fleshing it out ###

So let's get this sketched. We need
  * fixed levels 0, 1, 2, ...
  * level qualification _∀ n :: Level_
  * level lifting _(c+n)_, where c is constant
  * level functions? (doubtful) _n + n_
  * star lifting `*n`
  * lifting other level-polymorphic types? (doubtful, with the possible admissibility of `§`, i.e. _constraint_ kinds)

_Idea: Can we make level a special kind? That is present at all levels? Then these qualifications would appear in the telescope._

### Singleton Types? ###

When there is an (_n_+1) level of some data type, chances are good that it can be used as a parameter to the level _n_ singleton type. Elsewhere I suggest `Typ°` as the generated name for the singleton type that is parametrized in `Typ`.

# Implementation #

I have started filling the space spawned by ideas with code: https://code.google.com/p/omega/source/browse/trunk/tests/Iceberg.prg

## Status ##

We can compute fibrations by level. We can select by level and/or name.

Still to do:
  * signatures
  * cutoff in fibrations (detect highest constant in set and loop back)
  * typed/kindedness checks
  * inference
  * two-level formalism (structure functors?)
  * singleton types

# Bibliography #

## Mendler Style Recursion Combinators ##

http://kyagrd.dyndns.org/wiki/MendlerStyleRecursionCombinators