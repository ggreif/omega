* Functional Programming for Assurance and Performance

 - assurance: are we faithfully implementing the specification
 - performance: at *coding time* and *run-time*

** What is FP?

 - mathematical functions
 - origins: lambda calculus

** Typed Calculi

 - computation cannot go wrong
 - (local) inference


** Immutability

There is no concept like "Changing a value", but
 - you can _call a function_ with a different input (then it appears
   to be changing)
 - rebuild a new value _from parts_ of an old one

Why: Conceptual simplicity, deterministic, performant on modern HW

Swift: Value types.

** Datatypes and Algorithms

These "go together like a horse and carriage"!
https://www.youtube.com/watch?v=xtS46Wfsxnw

The 'Option' type

> data Option a = None | Some a

In Swift

enum Option<T> {
  case None
  case Some(a)
}

> data Dialect = US | British

*** Sums of products

Summands: *distinguishable* cases
Products: (possibly empty) tuple of *payload*

*** Pattern matching

The process of opening a value up:
 - determining the case
 - getting hold of the payload
 - (bringing constraints into scope)

*** Function types

> greeting :: Dialect -> Option String -> String
> greeting British None = "Good morning Sir!"
> greeting British (Some person) = "Good morning "++ person ++ "!"
> greeting US None = "Hi!"
> greeting US (Some person) = "Hi "++ person ++ "!"

** Parametricity

Works for every =T=

Brings compositionality and correctness.

** Applications

*** QuickCheck
 
