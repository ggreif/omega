
---

# Introduction #

Consider the `Nat'` datatype:

```
data Nat' :: Nat ~> *0 where
  Z :: Nat' Z
  S :: Nat' n -> Nat' (S n)
```

where `Nat` is defined thus:
```
data Nat :: *1 where
  Z :: Nat
  S :: Nat ~> Nat
```

This is a very common pattern of defining _singleton types_ in Ωmega. Its essence is that a _level n+1_ type is used to index an isomorphic _level n_ datatype, descending down to _level 0_.

But sometimes _n_ becomes more than 1 and the definition at the different levels gets very tedious, which is aggravated by the fact that new names must be invented for levels _n > 1_. `[`Witness the 2008 Summer School video and progress proof.`]` Our idea is to extend Ωmega's syntax with two multi-level definition constructs that hopefully take out the tedium of these patterns and make them enjoyable.

Actually there is some dogmatism here, because we want to keep the _phase distinction_, that is an intuitive virtue, which has brought us so far. It also appears as a _future work_ item at the end of `[`Sheard,Hook,Linger`]` as _Deriving Singleton types_.


---

# Proposal #

We define a syntax for _descending-levelled_ datatype definitions first. Then, in the spirit of Monnier's suggestion, add the syntax for descending-level _functions_, that is define the rule system at the highest applicable level (where no indices appear yet) and then the lower level equations are derived automatically. Finally we perform the fixpoint trick and introduce these once more but rooting at infinite level (`*∞`). `[`McBride`]` also makes an attempt to economize on typing mostly similar definitions by lifting types to the kind level. To this end he uses braces `{Type}` and accepts this as type indexes. But his setting (_she_) is pretty different as he preprocesses code annotated in such a way and emits Haskell for GHC's consumption. All lifted kinds then get replaced with `*0`.

## Defining data types rooting at `*n` ##

Consider the following syntax:
```
data ‹Nat› where
  Z :: Nat
  S :: Nat ~> Nat
```

This definition is actually a multi-level definition: `Nat :: *1` and `‹Nat› :: Nat ~> *0`. The constructors are given at the highest applicable level, here: `Z :: Nat :: *1` and `S :: Nat ~> Nat :: *1`, but implicitly define the object-level ones, `‹Z› :: ‹Nat› Z :: *0` and `‹S› :: ‹Nat› n -> ‹Nat› (S n) :: *0` too.

Of course, by adding more angle quotes we can root the construction higher up in the level hierarchy.

## Defining functions at the highest level and descending ##

A common annoyance in Ωmega is that type-level functions must be defined first before object-level functions can be defining that use the former for index calculation `[`Monnier`]`. Our syntax comes in here too.

```
‹plus› :: ‹Nat› -> ‹Nat› -> ‹Nat›
{plus Z n} = n
{plus (S m) n} = S {plus m n}
```

Again, the type rule mentions the lowest applicable level, while the equations are written out for the highest applicable level. Please note that the typing invokes the descending level shorthand notation and defines the following functions:
| **Level** | **Name** | **Signature** |
|:----------|:---------|:--------------|
| `*1`      | `plus`   | `Nat ~> Nat ~> Nat` |
| `*0`      | `‹plus›` | `‹Nat› m -> ‹Nat› n -> ‹Nat› {plus m n}` |
Also this level shorthand in the type rule is the distinguishing factor that teaches Ωmega to create a multi-level function definition.

## Rooting below `*∞`: the fixpoint ##

Now it is not always appropriate to have a finite cutoff for the indexing hierarchy, so similarly to the `*n` hierarchy we introduce a syntax for the fixpoint construction:

```
data «Foo» where
  Bar :: «Foo»
  Quux :: «Foo» ~> «Foo»
```

This syntax uses the _guillemets_-style double quotes. They remind us that there is actually an isomorphic parameter from a level one up present.

The types arising at any level are _finite_, and it is certainly possible to create values `Bar` or `(Quux Bar)` at any level. Here is how things line up:
| **Level** | **Name** | **Signature** |
|:----------|:---------|:--------------|
| `*n`      | `Foo`    | `Foo p ~> *n` |
| `*n`      | `Bar`    | `Foo Bar`     |
| `*n`      | `Quux`   | `Foo n ~> Foo (Quux n)` |
| _types_   | `Bar`    | `Foo Bar`     |
| _types_   | `Quux`   | `Foo n -> Foo (Quux n)` |


---

# Outlook: Pi in the Sky Programming #

All programs not mentioning `°`, `‹‹...››` or `‹...›` automatically also live in the _sky_, i.e. `*∞`, unless they are earth-bound (e.g. the `IO` monad). But there is a free flow of identifiers, bidirectionally.

Earth bound programs are also available in the sky, but cannot appear `::`-n raised for a determined n.
Otherwise a sky program may occupy any level as long as everything is neatly stratified (exclusion of circularity which could lead to [paradoxa](http://www.google.de/search?q=girard's+paradox)).

We obtain a form of dependent programming, which allows both styles, but the ultimate proving ability is not available when programming in the sky, one has to descend. The sky programs are elaborated to the GADT-only ones and all type-checking happens there. When pretty printing, we try to always output the sky program.

```
S (S Z) :: Nat -- in the sky
°S (°S °Z) :: Nat° (°S (°S °Z)) -- at level n
```


---

# Implementation Sketch #

Here I hope to summarize all the places in the current code base that would be affected by a possible addition of this feature. First, of course all the minor nuisances which I have discovered (see the comments in the [below](#Examples.md) examples) need to be overcome. I am slowly working on that, and issues exist.

## Parsing ##

The Parsec-based parser should be easy to extend (save the Unicode part) to accommodate the `<>` quoting. This could be an intermediate step to get a surface syntax. Unicode can follow later.

## Elaboration ##

For the finite case the elaborator must verify some things such as that there are no level annotations on the GADT, compute the upmost level, modify the `Dec` for the lower copies and feed them in.

For the fixpoint case the level-isomorphic kinding declaration must be fabricated.

All constructor functions must be visited and type indexes inserted.

## Type Checking ##

Nothing to do for the finite case. Optionally, instead of elaborating all the `forall`s one could perform an inference pass to fill those in.

For the `*∞` case, however, the level-isomorphic kinds must be introduced to the type checker. They are in a sense generalizing the `Star` hierarchy, which begin at kind level and have an isomorphic copy at each level above.

In our case the isomorphism would hold between `Foo p ~> *n` and `Foo q ~> *(n+1)` where the latter (after saturation) parametrizes the former, etc., at each level. The unification algorithm must be taught to deal with this construct and to not climb levels indefinitely. For being able to tie the kind knot, the translation environment for the GADT kinding must be extended to include the name pointing to the level-isomorphic kind.

Similarly for the function side of the medal.

## Exhibiting ##

This is just simple matter of programming.


---

# Open Issues #

  * Do we need unicode to spell out these new syntactic entities?
  * How can we fit this syntax into the pun that is used to call things from value and type levels the same? Can we automatically add the angle quotes?
  * Support the Haskell-like notation `data ‹Nat› = Z | S Nat`. Suggested by Edward Kmett. Makes sense, because at highest level the GADT-ness is seldom needed.
  * Should we employ a Tick-like syntax for raising levels? I.e.
```
data Foo^ = ... -- fixpoint introduction

data Bar^6 = ... -- rooted at *6

foo :: Bar^3 -- pick the one under *3
-- the syntactic/semantic identity Baz^0 ≡ Baz holds
```
  * What is more intuitive, using the type arrows (->) or kind arrows (~>) in the auto-levelled definitions? _Probably the latter as this is what level-universal definitions do now in Ωmega. In the stratum of values the arrows get converted automatically._
  * Namespaces. When I have `plus` rooted below `*∞` and also another definition of `plus` defined in stratum n > 0, then we cannot see the former in stratum n because of shadowing. So we need a means to grab it from the namespace below, where it must be unique. Haskell uses the `'`-prefix for this purpose, which is unfortunately part of the identifier syntax. We could use the `⌊plus⌋` bracketing to grab from the lower and `⌈plus⌉` from the upper namespace.


---

# References #
  1. http://www.iro.umontreal.ca/~monnier/comp-deptypes.pdf
  1. [Tim Sheard's 2008 Lecture Video](http://www.cs.uoregon.edu/research/summerschool/summer08/video/July26Lect1.wmv)
  1. http://code.google.com/p/omega/source/browse/trunk/tests/Progress.prg
  1. http://personal.cis.strath.ac.uk/~conor/pub/she/fun/talk.pdf
  1. [GADTs + Extensible Kinds = Dependent Programming by Sheard, Hook and Linger](http://web.cecs.pdx.edu/~sheard/papers/GADT+ExtKinds.ps)
  1. [Programming with Term-Indexed Types in Nax by Ahn, Sheard, Fiore and Pitts](http://nax.googlecode.com/svn/trunk/draft/IFL12draft.pdf)
  1. [Parametricity and Dependent Types, by Bernardy, Jansson, Paterson](http://www.soi.city.ac.uk/~ross/papers/pts.pdf)
  1. [Monnier & Haguenauer, Singleton Types Everywhere](http://www.iro.umontreal.ca/~monnier/comp-deptypes.pdf)

---

# Examples #

## Ωmega example for `‹‹Pat››` ##

`‹‹Pat››` is like `‹Nat›` but rooted under `*2`:
```
data Pat :: *2 where
  Y :: Pat
  Q :: Pat ~> Pat
 deriving Nat(p)

data Pat' :: Pat ~> *1 where
  Y' :: Pat' Y
  Q' :: Pat' n ~> Pat' (Q n)
 deriving Nat(q)

data Pat'' :: Pat' p ~> *0 where
  Y :: Pat'' Y'
  Q :: Pat'' n -> Pat'' (Q' n)
 deriving Nat(r)
```
We can see that all is pretty regular.

Testing:
```
prompt> Q (Q Y)
2r : Pat'' 2q
```

_Note: [Issue 70](https://code.google.com/p/omega/issues/detail?id=70) is hindering us rooting this under `*3`._

_Update: When spelling out all the `forall`s explicitly, Ωmega accepts roots even more levels up: see [AutoLevelled.prg](http://code.google.com/p/omega/source/browse/trunk/tests/AutoLevelled.prg?spec=svn514&r=514), but of course it gets messy._

## Ωmega example for `‹‹plus››` ##

```
plus :: Pat ~> Pat ~> Pat
{plus Y n} = n
{plus (Q m) n} = Q {plus m n}

plus' :: Pat' m ~> Pat' n ~> Pat' {plus m n}
{plus' Y' n} = n
{plus' (Q' m) n} = Q' {plus' m n}

plus'' :: Pat'' m -> Pat'' n -> Pat'' {plus' m n}
plus'' Y n = n
plus'' (Q m) n = Q (plus'' m n)
```
Again, this is nice and regular.

_Note: unfortunately this does not compile with Ωmega 1.4.3 due to [issue 23](https://code.google.com/p/omega/issues/detail?id=23) :-(_

_Update: should work with Ωmega 1.4.7pre :-)_

## Ωmega example for `«Foo»` ##

`«Foo»` has an isomorphic copy at every level up to infinity, we can tentatively sketch a definition here, not sure if the circularity is accepted:
```
data Foo :: level n . Foo p ~> *n where
  Bar :: Foo Bar
  Quux :: Foo p ~> Foo (Quux p)
 deriving Nat(f)
```
Level 0 is standard.

_Note: it does not compile (with v1.4.6)_
```
While parsing a type constructor, unknown type: Foo
```

## Ωmega example for `‹‹Maybe››` ##

http://code.google.com/p/omega/source/browse/trunk/tests/SingMaybe.prg

If we had the strange recursion, it would look like

```
data Mayb :: level n . Mayb a ~> *n ~> *n where
  Noth :: Mayb Noth a
  Jus :: a ~> Mayb (Jus a) a
```

Of course assuming `(~>)` is level-preserving (which Ωmega 1 is _not always_).

## The use of the additional type index ##

The additional index can be used to
  * [derive strictness](SingletonStrictness.md)
  * type-based termination
  * return value discrimination depending on input types (terminating?, inductively-sequential?, lemmata needed?)
  * [swappable type-checking regimes](http://www.reddit.com/r/haskell/comments/1ht33e/bottomup_type_annotation_with_the_cofree_comonad/caxzuqu)

What when we have a purely run-time (level 0) function definition for such an algebraic type?
Then the algorithms simply run in the `Hidden Foo` mode:
```
case foo of
Hidden Bar -> return $ Hide 25
Hidden (Quux p) -> return $ Hide 42
```
Which has type `Hidden Foo°` and behaves like a regular `Foo` in Haskell. The recursive occurrences become hidden too (_but by which mechanism?_).

C.f. the `nax` paper.

Intuitively the `°` separates the _semantic_ portion of the type from the _ad-hoc_ portion. The ad-hoc part is directly intended by the program author, and the Hindley-Milner type inference is acting on this part. The semantic portion is however the bridgehead enabling analyses and isomorphisms to be established. For example the if we can establish an isomorphism of the semantic portions of two values that represent the same value (e.g. `S (S (S Z)))` and `3`, then we can verify a conversion function.

An appealing idea is to consider `(°)` as a type former that can be omitted (left argument is inferrable), and separating the (natural side) user-defined arguments from the (negative side) semantic arguments. At position -1 one would find the isomorphic reflection of the (known part of the) value into the type level.

So, in summary, one would write in the sky
```
data Prime :: Nat -> * where
  Joined :: a -> Factorize a -> Prime a
```

which would be rewritten to be level-conscious as
```
data Prime :: level k . Prime n ° (n ° Nat) ~> *k where
  Joined :: (a ° Nat) ~> Factorize a ~> Prime a
```

In the levelled form only the `(a ° Nat) ~>` splitting is necessary, this looks like  a Pi, but is equi-levelled.

In the sky syntax `a :: Nat :: *1` via the kind declaration (and as such uninhabited), but actually a value-level object `a :: (a ° Nat)` via the `Joined` constructor. The type argument at position -1 takes care of the level business.

(°) binds just an ε less than (~>).

## The function types ##

With he above scheme the function arrow becomes a type constructor synonym
```
type a -> b = exists a' b' . a°a' ~> b°b'
```
But wait! We could add more hidden type indices, e.g. one that describes the internal structure of the function definition and all that stuff. Finally we could introduce a typeclass
```
class Category (--+) => Compilable (--+) where
  compile :: a --+ b -> a -> b
```


---

# The Category of Patterned Types and Abiding Maps #

Objects are patterned types `p ° T` where `p` is a level-lifted inhabitant of `T` with possibly added _wildcards_.

Morphisms are maps `p°T ~> q°U` that abide the patterns `p` and `q` beside being functions from `T` to `U`. What does _abiding_ mean? We allow _relations_ between p and q, i.e. `S p == q`. Furthermore patterns can be _tensored_ to obtain the concept of a piecewise defined relation.

Identity and composition are defined in the usual way.

The forgetful functor from `Pat` to `Hask` just leaves away the patterns (and the necessity to abide to them) and keeps the types. This is equivalent to widening the patterns to the _anonymous accept all_ pattern `_`.

Contexts can now trivially contain definitions, e.g.
```
Γ = {x :: (Cons 4 Nil ° [Nat])}
```
Here `x` is _defined to be_ `Cons 4 Nil`. Mixing in proper patterns partially defines `x`.

## Questions waiting to be answered ##

Can we use _guarded patterns_, i.e. does this correspond to qualified types?

Do we need `::` in contexts? If yes, what extra expressivity is obtained by having both pattern variables and typed variables (besides these having shifted levels)?

This project has a similar notion of pairing types with a predicate on the values: https://github.com/tomprimozic/type-systems/tree/master/refined_types#readme

With the definition of _abiding_ do we cover _logical relations_?

What is the connection to [categories with families](http://www.cse.chalmers.se/~peterd/papers/InternalTT.pdf)? See definitions in 2.1.

When tensoring definitions we'd like to not get mired into order dependency. Ωmega1 solves this by requiring _inductively sequential_ definitions at the higher levels. Google for "Overlapping and Order-Independent Patterns" for a new definitional approach in Agda (by Jesper Cockx).