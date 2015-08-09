# Introduction #

Currently when we juxtapose expressions in Ωmega we get function application. Look at this: expression `map ord "Hello"`; once written you'll get value of `[Int]` and you cannot control the process. This is pretty much unavoidable, just like the type constraints that are imposed on `map` and `ord`.

We propose a new syntactical element that liberates juxtaposition from these fixed rules and allows us to assign semantics to it in a flexible fashion by the `do data` syntax.

## Why at all? ##

The most important reason is that we want to use the familiar syntax for constructing other types of data than executable code. For example we may want to write down hardware descriptions just like we do in Haskell. Of course we cannot (and usually don't want to) execute it, but capture it for later transformations.

The idea to this proposal came after digesting Wadler et al.'s paper about the _arrow calculus_. There he introduces _arrow applications_, _lambdas_ and _lets_. For each arrow, presumably.

Accidentally, in Haskell and Ωmega already use a similar mechanisms
  * namely on the right hand side of the `::` notation, where juxtaposition means application of kind arrows for parameterized data types (or type families/functions)
  * on the left hand side of equations, where juxtaposition means pattern construction and analysis
  * in Ωmega's `{typefun arg1 arg2}` brackets (or Haskell's _type family_ calls) it is type function application
  * following `type` or `data` keyword in definitions, the type parameters.

# Details #

We'll define the syntactical sugar for our proposed language feature and define its expansion. This is basically a restricted macro expander.

## The New Syntax ##

Here is an example:

```
do data (,) { "Hello" (ord map) }
  where do a b = b, a
```

This would expand to `((map, ord), "Hello") :: (((a->b)->[a]->[b],Char->Int), [Char])`.
The `where do` clause forces the AST builder to rearrange juxtapositions to their reversals inserting a comma in between, and the `do data (,)` determines that the the type rules are according to the _pair_ type constructor.

The equation after the `do` keyword must be a syntactically valid equation, with function-like pattern on the left side.

## Another Variant ##

Looking at the problem from another angle, Ωmega already has a way of building `Code`, namely with these brackets: `[| ... |]`. We can kill two birds with one stone by introducing a new kind of syntax derivation:

```
data Codigo :: * where
  Fun :: String -> Codgigo
  Apply :: Codgigo -> Int -> Codgigo
 deriving syntax(c) Code(Fun, Apply)
```

This allows us to write `[|"plus" 45 54|]c` and expands to `Apply (Apply (Fun "plus") 45) 54`.

The second bird we killed is _escaping_: using `$(...)` we can get out of the syntactic expansion's world and fall back to the semantics of the outer context.

## Lambdas? ##

This clause could change the lambda syntax' behaviour: `where do \x -> "x"` as an example of the "C" stringize operator.

In _code brackets_ these are  already present, we only need a new constructor, either
  1. `Abs :: Label var -> Codgigo -> Codgigo`, or
  1. `Abs :: String -> Codgigo -> Codgigo`.

## `let` definitions? ##

`where do let a = expr`

In _code brackets_ these are  already present, we only need a new constructor, either
  1. `Let :: Record (Row Tag *) -> Codigo -> Codgigo`, or
  1. `Let :: [(String, a)] -> Codigo -> Codgigo`.

The `where` clauses would map to `Let`.

## A Third Variant ##

A third idea hatched my mind, `derive syntax(ac) Applicative (App, Lam, Let)`.

In the meantime I have a good understanding on how such a thing could be implemented.

For example use the standard Ωmega parser to read everything between the following parentheses:
```
(let l = \x -> p in l m)ac
```
Then the _Applicative_ (here with an `ac` suffix) syntax extension walks the `Exp` tree and converts all
  * _Names_ (global variables at this point) get converted to `Label t` (or better `Var`s?),
  * abstractions to calls of constructor `Lam` with a `Label t` as the first argument and the `Exp` as the second,
  * parsed apply nodes get converted to `App` constructors, and
  * finally the (recursive) `let`s get mapped to `Let sym e1 e2`.

One could even convert `[expr]` to arrow units. The two forms of _escape_ would interface to the pure world.

Patterns seem feasible too.

# The `Closed` Type Class #

```
class Closed arr where
  type Domain arr
  type Codomain arr
  -- has a whitespace operator (juxtaposition)
  (``) :: Domain arr `arr` Codomain arr -> Domain arr -> Codomain arr
```

```
class instance Closed (->) where
  (``) :: ($)
```

# References #

  * http://web.cecs.pdx.edu/~sheard/papers/HFL07Sheard.pdf
  * http://homepages.inf.ed.ac.uk/wadler/papers/arrows-jfp/arrows-jfp.pdf