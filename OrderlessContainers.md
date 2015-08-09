# Introduction #

[Issue 6](https://code.google.com/p/omega/issues/detail?id=6) calls for `Set`-like data structures. Here we explore the design space a bit.

# Kinds of Orderless Data Structures #

Clearly these are _associative_ and _commutative_ both of which are at odds with our classical _constructor approach_.

I envision three semantic forms:
  * `Bag`s: these respect insertion and removal, i.e. size always updates. Duplicates are always preserved.
  * `Set`s: these respect removal, but cancel duplicated insertions.
  * A `Supply` respects insertions, but disrespects removals: added once, you can get it back any time.

In any case a pattern match with a head position that is not in the container will fail.

## Aside: Inductive vs. Coinductive ##

Inductive means: _you can always increase_, whereas coinductive means _you can always remove_. By this categorization `Supply` is the coinductive sister of `Set`.

## How to Deal with Pattern Match Failure ##

  1. we could live in a `Maybe`-like monad
  1. we could always wrap the pattern with `Just` (what is `Nothing` then?)
  1. only the `_` pattern matches an empty orderless container? Not a particularly good idea, since this is not inductively sequential (i.e. _type functions_ are out).
  1. having 3 constructors:
    * `Nil :: C a`,
    * `Cons :: a -> C a -> C a` meaning, yes I _found it_, and
    * `ComeBackLater :: C a -> C a -> C a` :-) Neither the left nor the right contain what you are looking for.

`ComeBackLater` should only occur in patterns. It could also be _nullary_.

### Non-joker semantics ###

I see one more alternative: Use `Cons` with a pattern (that has free variables) at the head position: matches something, but with an expression `$(expr)` or closed pattern we get a membership test.

## Use case for `Supply`s ##

Universal truths, proofs and similar _ideal_ terms are good candidates to be put into supplies. Resource-like things on the other hand are better suited for being contained in `Bag`s or `Set`s.

For example in a theorem prover one could move all proven propositions into a `Supply` and get them back any number of times. Of course this must happen in a referentially transparent manner, but that is an implementation detail.

# Implementation Details #

Let's think about how this stuff can be implemented...

We need a new _type class_ `ConstructorLike` which has instances for all these types of strange consructors and the classical ones too. It needs an operation `null`, _membership test_ and _splitting_.

## How do the Types/Kinds Vary? ##

Very important question is how the type of an object changes when we pattern-match on it. Clearly, the type will change when we have non-homogenous containers, i.e.
```
shorten :: {a; rest}ts -> rest
shorten {_; rest}s = rest
```
Here the suffixes `s` and `ts` mean value- and typesets respectively, with set-like semantics.

An interesting case is when some of the values differ but have the same type, in this case the type level cannot be set-like. Hmmm. Yes, sets at some level would be typed by bag-like semantics one level up. Unless of course when at insertion time the value gets discarded, but the type would increase when bag-like. This is not good.

Only for singleton types we would preserve the _set :: set_ relation.

The _bag :: bag_ appears like a safe bet, but we have to track which particular element below has which element in the upwards.

What about supplies?

# Surface Language #

Contrary to [InductionPrinciples#Set-\_and\_Bag-like\_Theorems](InductionPrinciples#Set-_and_Bag-like_Theorems.md) I now believe that we need a `deriving semantics` clause for `data` declarations. These would instantiate the exotic constructors.

# Connection to Species #

[Species](http://www.cis.upenn.edu/~byorgey/pub/species-pearl.pdf) are data types that quotiented out the automorphisms, that is only the data's shape counts. These perfectly describe `Set`s. Remains to clarify how they relate to `Supply`s and the rest.