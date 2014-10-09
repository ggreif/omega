> import Test.QuickCheck
> import System.IO.Unsafe

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

The 'Optional' type

> -- data Bool = True | False
> data Optional a = None | Some a

In Swift

enum Optional<T> {
  case None
  case Some(T)
}

data City = Manchester | London | ...

> data Dialect = US | British
> --- data Dialect = 1 + City * Bool

enum Dialect {
  case US
  case British(city: City, downtown: Boolean)
}

*** Sums of products

Summands: *distinguishable* cases
Products: (possibly empty) tuple of *payload*

*** Pattern matching

The process of opening a value up:
 - determining the case
 - getting hold of the payload
 - (bringing constraints into scope)

*** Function types

> greeting :: Dialect -> Optional String -> String
> greeting British None = "Good morning Sir!"
> greeting British (Some person) = "Good morning, "++ person ++ "!"
> greeting US None = "Hi!"
> greeting US (Some person) = "Hi "++ person ++ "!"

** Parametricity

Works for every =T=

Brings compositionality and correctness.

Examples: =map=, =foldr=

** Applications

*** QuickCheck

> prop_foldr as = foldr (+) (1::Int) as == sum as


Consider this homework:

        +-------+
        |  17   |
    +-------+-------+
    |       |   9   |
+-------+-------+-------+
|       |   3   |       |
+-------+-------+-------+

Let's generate these for the pupil...

import Test.QuickCheck

        +-------+
        |   c   |
    +-------+-------+
    |   a   |   b   |
    +-------+-------+

> prop_tri a b c = sum (map (maybe 1 (const 0)) [a, b, c]) == 1
>                 ==> tri a b c == unsafePerformIO (pupil a b c)

> tri (Just a) (Just b) Nothing = a + b
> tri Nothing (Just b) (Just c) = c - b
> tri (Just a) Nothing (Just c) = c - a

> pupil (Just a) (Just b) Nothing = do putStrLn ("a = " ++ show a ++ "  b = " ++ show b)
>                                      fmap (read :: String -> Int) getLine
> pupil Nothing (Just b) (Just c) = do putStrLn ("b = " ++ show b ++ "  c = " ++ show c)
>                                      fmap (read :: String -> Int) getLine
> pupil (Just a) Nothing (Just c) = do putStrLn ("a = " ++ show a ++ "  c = " ++ show c)
>                                      fmap (read :: String -> Int) getLine