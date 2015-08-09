# _Upcoming_ Release 1.5.4 #

Nothing notable yet.


---

# _Upcoming_ Release 1.5.3 #

## New Feature: `Applicative` Syntax Extension ##

The new syntax extension, like e.g. `Pair` and `LeftRecord`, will map standard application and lambda syntax to a data type:
```
data Expr = App Expr Expr
          | Lam (Label l) Expr
          | Var (Label l)
          | Let (Label l) Expr Expr
  deriving Applicative(lc)
```

Now you can write terms in regular syntax in parentheses suffixed by `lc`, and they'll be translated into the `Expr` data type:
```
(let a = \a -> a a in a a)lc
 ----> Let `a (Lam `a (App (Var `a) (Var `a))) (App (Var `a) (Var `a))
```

Ωmega will take care of pretty printing them too (unlike in the response above) and you'll be able to escape out into the surrounding world by a wormhole that is opened by `$(...)`.

This feature is very little tested, please report problems if you encounter any.

See some of the design ideas on the wiki: IntensionalApplication.

## New Feature: Source-file Determined Bounds ##

Using the syntax
```
##bounds backchain 10
```
in a program file, the given bound can be _increased_ to fit the typechecker's need for the problem at hand. The bounds cannot be _decreased_.

## Bugs fixed ##
  * [Issue 107](https://code.google.com/p/omega/issues/detail?id=107), which caused backchaining to fail when one alternative (of ambiguous solutions) was refutable, while others succeeded.
  * [Issue 108](https://code.google.com/p/omega/issues/detail?id=108), caused the type checker to error out because the outer binding was not in scope.
  * [Issue 111](https://code.google.com/p/omega/issues/detail?id=111), rejected GADT definitions that had `L` or `R` constructors, even if these never affected the value stratum.
  * [Issue 59](https://code.google.com/p/omega/issues/detail?id=59), codebase modernized.


---

# Release 1.5.2  _(2013-08-21)_ #

## New Feature: Parser Combinators ##

Finally the `Parser` type constructor is worth something. Some basic combinators are available in the `Parsing.prg` module. Of course you can build on top of them.

## Bugs fixed ##
  * [Issue 105](https://code.google.com/p/omega/issues/detail?id=105), what Ωmega outputs is now more in line with what it expects the user to type in.


---

# Release 1.5.1 _(2011-09-07)_ #

Ωmega v1.5.1 is mainly a bugfix and infrastructural release. We have built some fundament on which we can base new features in the close future and get releases out faster.

Now, read on for the news...

## On Hackage Now ##

We are now downloadable from [Hackage](http://hackage.haskell.org/package/omega-1.5.1).
Please use your [favorite](http://www.haskell.org/cabal/) Haskell package manager to install Ωmega automatically! This gets us close to resolving [issue 92](https://code.google.com/p/omega/issues/detail?id=92) :-)

## New Feature: _Backquoted_ Operators at the Type Level ##

Similar to Haskell, type constructors and type function calls can now be written with a backquoted  infix name between the arguments, like this
```
Eq :: n `Equal` {m `plus` k}
```

## Bugs fixed ##
  * [Issue 65](https://code.google.com/p/omega/issues/detail?id=65), lots of ugly interactions between reserved words and expressions have been rectified.
  * [Issue 89](https://code.google.com/p/omega/issues/detail?id=89), incorrect scoping of expression annotations is now corrected.
  * [Issue 91](https://code.google.com/p/omega/issues/detail?id=91), a remedy has been incorporated, but this is not the final fix. We display a warning for now.
  * [Issue 93](https://code.google.com/p/omega/issues/detail?id=93), causing a compile error on the GHC 7.x compilers has been fixed.
  * [Issue 94](https://code.google.com/p/omega/issues/detail?id=94), a problem inferring the second component of types involving impredicative types has been fixed.


---

# Release 1.5 _(2011-04-29)_ #

Release 1.5 marks the first milestone without major involvement of [Tim](http://code.google.com/u/@UBJVQVdRBxdNWwR9/), who is directing his attention towards [Trellys](http://code.google.com/p/trellys), a compiled language with dependent types. Big thanks to him for all the awesome work on Ωmega in the past, we will miss his vision, wisdom an profound understanding of the matter. With some luck he can still contribute an occasional fix here or there.

## Licensing ##
The highlight of this release is the change of licensing terms to become a pure 3-clause BSD license. Previously an additional clause prohibited use in commercial settings without written consent ([issue 74](https://code.google.com/p/omega/issues/detail?id=74)).

## Syntax ##
Additional syntax extensions can be derived. These include:
  * left-associative variants to `Pair`, `List` and `Record` (spelled as `LeftPair` etc.)
  * nullary `Unit` and unary `Item` extensions

## Reactivated Feature: Pointers ##

Code present (but commented out in the sorces) has been cleaned up and re-enabled. Following primitive functions are now available:
```
initPtr :: forall a b . Ptr a -> b -> IO (Equal a b)
newPtr :: forall a . IO (Ptr a)
nullPtr :: forall a . Ptr a -> IO Bool
readPtr :: forall a . Ptr a -> IO (Maybe a)
samePtr :: forall a b . Ptr a -> Ptr b -> IO (Equal a b)
writePtr :: forall a . Ptr a -> a -> IO ()
```

Alas, the manual does not mention them, yet. This should be rectified in an upcoming release.

## Bug Fixes ##
Many bugs have been fixed, most notably displaying higher-rank ([issue 75](https://code.google.com/p/omega/issues/detail?id=75)) and arrow ([issue 83](https://code.google.com/p/omega/issues/detail?id=83)) types. Thanks for the attached patches we received!

## Obtaining the Release ##
Please visit [the downloads tab](http://code.google.com/p/omega/downloads/list) for getting the sources. You will need a modestly recent GHC to compile it.

## Format of the Download Archive ##
The `Omega15` file has been compressed by following commands (on a linux machine)
```
zip -v -r Omega15 distr -x \*.pdf -x \*.ps --to-crlf
zip -v -u Omega15 distr/*.pdf distr/*.ps
```
So all text files are with CR/LF line endings but the `.pdf` and `.ps` ones, which are left binary.


---

# Older Releases #

Please visit Tim's [download page](http://web.cecs.pdx.edu/~sheard/Omega/index.html) to obtain information about past releases.