# Functional Programming #

Name: _functional_ means an operation receiving a function as an argument.

Putting this paradigm/idiom to work for computing is a very old trick.

Should not be confused with _procedural_ programming.

## Haskell ##

  * History (academical, _programming language research_ vehicle)
  * Popularity ([on IRC](http://www.haskell.org/wikiupload/a/a4/Nick-activity.png), [compared to others on reddit](http://langpop.com/#reddit))
  * Resources ([reddit](http://haskell.reddit.com), [haskell.org](http://haskell.org))
  * Tutorials, Books ([LYAH](http://nostarch.com/lyah.htm), [RWH](http://book.realworldhaskell.org/))
  * Search engine [Hoogle](http://www.haskell.org/hoogle/)

# Equations #

We can always _substitute equals for equals_. Just as in _[mathematics](http://www.jfsowa.com/logic/math.htm)_.

A program contains **equations**
```
fib 0 = 1
fib 1 = 1
fib n = fib (n - 2) + fib (n - 1)
```

Now we can ask for `fib 3`:
```
fib (3 - 2) + fib (3 - 1)
```
≡
```
fib 1 + fib 2
```
≡
```
1 + fib 2
```
≡
```
1 + (fib (2 - 2) + fib (2 - 1))
```
≡
```
1 + (fib 0 + fib 1)
```
≡
```
1 + (1 + 1)
```
≡
```
1 + 2
```
≡ ```
3```
# Types and Data #

_Sum of products_ covers:
  * enumerations, alternatives: ```
data Weekday = Monday | Tuesday | ...```
  * named tuples: ```
data Student = Stud Int String```
  * a mixture of the above: ```
data Bandwidth = Odu0 Int | Odu1 Int Int | Odu2 ...```

## Pattern Matching ##

gives _names_ to enclosed data pieces:
```
case stud of
  Stud jahre name | jahre > 30 -> name ++ ", du bist zu alt!"
  Stud jahre _    | jahre < 20 -> "ein Frischling"
  Stud jahre name -> "mit " ++ show jahre ++ " hat man noch Träume, " ++ name
```

## Deriving ##

Practical details
```
data Color = Red | Green | Blue
  deriving (Show, Read)
```

Automatically generates code so that `Color` values can be converted to/from text.

# Functions #

Two connecting points and something in-between:

![http://upload.wikimedia.org/wikipedia/commons/3/3b/Function_machine2.svg](http://upload.wikimedia.org/wikipedia/commons/3/3b/Function_machine2.svg)

> Functions are first-class!

They
  * can be passed, and
  * can be returned
from other functions.

## Function types ##

```
foo :: Int -> Bool -> [Char]
```

This tells us that `foo` is a function that accepts an
  1. _integer_ (of machine word size, called `Int`)
  1. a _boolean_ (named `Bool`)
in this order, and results in a _list of characters_ (written as `[Char]` or `String`).

These are also called _arrow types_, and they associate to the right:
```
Int -> (Bool -> [Char])
```

## Partial application ##

No necessity to give _n_ arguments to an _n_-ary function:
```
elem 'Z' :: [Char] -> Bool
```

## Composition ##

As long as types match, we can join the connection points of functions:
```
not . null . filter (/= 0)
```

## Lambda ##

Anonymous functions can be obtained
  * as _sections_, e.g.  `(3 *)` or `(a -)`
  * as _lambda expressions_, `\ a b → a * c + b`

May capture local variables in scope.

## Combinators ##
  * Parsing/pretty-printing
  * Database queries
  * SVG [diagrams](http://pnyf.inf.elte.hu/fp/Diagrams_en.xml)

### Typical combinators ###

Combinators are pre-made functions that are
  * useful in many situations (i.e. _generic_), and
  * compose gracefully to bigger programs

#### `map` ####
```
map :: (a -> b) -> [a] -> [b]
```
![http://www.cs.berkeley.edu/~bh/v1ch5/map.gif](http://www.cs.berkeley.edu/~bh/v1ch5/map.gif)

#### `filter` ####
```
filter :: (a -> Bool) -> [a] -> [a]
```
![http://www.cs.berkeley.edu/~bh/v1ch5/filter.gif](http://www.cs.berkeley.edu/~bh/v1ch5/filter.gif)

#### `foldr` ####
```
foldr :: (a -> b -> b) -> b -> [a] -> b
```
![http://upload.wikimedia.org/wikipedia/commons/3/3e/Right-fold-transformation.png](http://upload.wikimedia.org/wikipedia/commons/3/3e/Right-fold-transformation.png)

# Laziness #

By default expressions are evaluated the first time they are needed.

> From then on they are caching the result.

```
main = do { putStrLn pi; putStrLn pi }
  where pi = computePi 1000
        computePi digits = ...
```

## Infinite data ##

Laziness makes it possible to create infinite lists
and
  * only consume a finite prefix, or
  * create non-terminating programs around them.

## List comprehensions ##

Several notational elements aid the manipulation of (infinite) lists
```
take 10 [ (i,j) | i <- [1..], j <- [1..i-1], gcd i j == 1 ]
```

# Types #

Types determine which expressions are accepted.

> [Well-typed programs cannot go wrong](http://www.informatics.sussex.ac.uk/users/mfb21/interviews/milner/)

## Type annotation by ‘`::`’ ##

The symbol `::` is pronounced as “has type”.

## Type inference ##

The Haskell implementation collects all constraints and tries to solve them.

In the process it assigns types to _identifiers_ and subexpressions:
```
if foo b then "GO!" else b
```

Constraints collected:
  * `foo :: α → β`, because it is applied to an argument, i.e. it must be a function
  * `foo b :: Bool`, because it is the `if` condition
  * `b :: α`, because it is argument to `foo`
  * `foo b :: β`, because it is the result type of `foo`
  * `b :: [Char]`, because the `else` leg must have the same type as the `then` leg

So we can infer `α ≡ [Char]`, `β ≡ Bool` and `foo :: [Char] → Bool`. The whole expression is `[Char]` typed.

## Built-in rules ##

Each `data` definition contributes to the built-in typing rules.

All language constructs come with their obvious rules for deriving constraints:
  * `if`
  * `case`
  * etc.

# Side Effects and their Control #
> All expressions are built in a pure way, i.e. there are no side effects.

> Side effects may arise when expressions are `run`.

> `run` encapsulates effects and does not let them escape.

## What are side effects? ##

> When the same expression results in (potentially) different answers:
  * mutable state (i.e. global variables)
  * input/output
  * (catching) exceptions

## The world of `IO` ##

_Imperative programmers_ mostly program in this world.

In Haskell, input/output actions have a distinguished type:
```
getChar :: IO Char
```

This `IO` wrapper cannot be peeled off!

Only by connecting an (elementary or complex) `IO` action to the `main` name can we run this action, and thus obtain its side effects.
```
main :: IO a
```

### Best metaphor ever ###

Wrapping a _payload type_ inside `IO` serves as a [barrier device](http://upload.wikimedia.org/wikipedia/commons/0/04/Kondom.jpg).

## Other side effects ##

Stateful computations (e.g. many _graph algorithms_) `ST`

Software Transactional Memory `STM`

# Sequencing #

Formalization of _former_ and _latter_.

Related, but not restricted to side effects.

## Programmable semicolon ##

For every _type wrapper_ (such as `IO`)
  * an entering operation `return :: α → Θ α` and
  * a sequencing operation `>>= :: Θ α → (α → Θ β) → Θ β`
can be defined.

Sometimes this is already defined for you!

## Example: `Maybe` ##

```
data Maybe a = Nothing | Just a
```

We overload `return` by
```
return :: a -> Maybe a
return a = Just a
```
and `>>=` like this
```
(>>=) :: Maybe a -> (a -> Maybe b) -> Maybe b
Nothing >>= _ = Nothing
Just a >>= transform = transform a
```

[Maybe](http://hackage.haskell.org/packages/archive/base/latest/doc/html/Prelude.html#t:Maybe) is defined in the _standard prelude_ and available as a very simple error reporting mechanism.

## `do` notation ##

Nicer way than sequencing in terms of `>>=` is writing semicolons :-)
```
do { subjekt <- versteheSubjekt
   ; prädikat <- verstehePrädikat
   ; objekt <- versteheObjekt
   ; return (Satz subjekt prädikat objekt)
   }
```

# Surprising uses #

Domain-specific Embedded Languages, _EDSLs_

  1. Executable Specifications
    * [seL4 microkernel](http://ertos.nicta.com.au/research/sel4/tech.pml)
  1. HW-Description
    * [Kansas Lava](http://www.ittc.ku.edu/csdl/fpg/Tools/KansasLava)
    * [Reduceron](http://www.cs.york.ac.uk/fp/reduceron/)
  1. Embedded, realtime ([Copilot](http://hackage.haskell.org/package/copilot), [Atom](http://hackage.haskell.org/package/atom))

# Demo #

  1. GHCi Demo
  1. [TryHaskell](http://tryhaskell.org/)
```
  foldr (*) 1 [42,13,22]
```

# Where are the Benefits? #

Security by
  1. static type discipline

Efficiency by
  1. pureness, default immutability
  1. easier to parallelize to many cores
  1. no locking necessary

Economy by
  1. powerful combinator libraries
  1. type inference, i.e. no type annotations required

# Who uses Haskell/FP? #

A growing body of companies depend on functional programming
  * in industry: http://www.haskell.org/haskellwiki/Haskell_in_industry
  * at ALU: http://cufp.org/conference/sessions/2011/fourteen-days-haskell-real-time-programming-projec

# Credits #

  * Images from [WikiPedia](http://wikipedia.org) and [Brian Harvey](http://www.cs.berkeley.edu/~bh)'s online lectures.

  * HTML stolen from [Bryan O'Sullivan](http://bos.github.com/strange-loop-2011/slides/slides.html)

# Questions? #