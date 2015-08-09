# cf. Paper "A tutorial impl ... pattern unification" (Gundry, McBride) #

  * Dependent sums are like key and lock: the knowledge of the first projection (having the key) implies the knowledge of the **type** of the second projection (can open the lock), so we can do something useful with it.
  * Have mixed PHOAS/deBruijn terms where indices hint at the presence and provide (p,B) <==> (P,b) converions; x: _has no X_, X: _may have X_.
  * use item notation thrists to serialize expression trees
  * use apply thrists for {argument, π<sub>1</sub>, π<sub>2</sub>} (see Figure 1.)
  * use TH to embed real Ωmega fragments into Haskell code (parser!!), as Iceberg: `[Ω|data Nat' ...|]`, and a special quotation to do the type checking and codegen. Free LLVM backend!
  * we can already explode `Label`s to thrists of one-character tags by using
    1. `newLabel :: [Char] -> HiddenLabel`, and
    1. `sameLabel :: Label a -> Label b -> Equal a b + DiffLabel a b`.
  * surprise: we can also re-assemble the original label from the thrist in the same way!


---

# cf. Paper "Elaborating Inductive Definitions" (Dagand, McBride) #

## Defining types by inductively sequential functions ##

From what I absorbed in the first pages, there is a clear correspondence between
```
data Vec :: * ~> Nat ~> * where
  Nil :: Vec a 0t
  Cons :: a -> Vec a n -> Vec a (1+n)t
```
and the corresponding inductively sequential function
```
vec :: * ~> Nat ~> *
{vec a 0t} = Vec a 0t
{vec a (1+n)t} = a -> Vec a n -> Vec a (1+n)t
```

_Aside: what happens when `{vec ...}` appears in the RHS?_

The say that instead of writing datatype definitions, it is cooler to write such a type function and this allows a lot of automation. Think `deriving` in Haskell.

## Connection to the Iceberg ##

The surface syntax of Ωmega could extract (or even allow) such functions to simplify the construction.

```
vec :: (* ~> Nat ~> *) ~> * ~> Nat ~> *
{vec t a 0t} = t a 0t
{vec t a (1+n)t} = a -> t a n -> t a (1+n)t
```

Here the `t` parameter would be `Iceberg ‹Vec›` or such.

_Aside: the signature above looks suspiciously like that of indexed functors._

Drop in a `Tag` into `vec`'s signature, and have _constructor names_ too.

## Connection to `prop` ##

[Issue 107](https://code.google.com/p/omega/issues/detail?id=107) stipulates that the proof engine currently only can deal successfully with `prop`ositions where the rules are in sequentially inductive form. For these a clear decision procedure exists. But the `prop`s where this is not give are also useful. These require another type of backtracking. Could this dissonance be resolved?

## Connection to primes ##

Can we come up with a prime-based check for verifying _inductively sequentialness_?

Here is the idea:
  * `n` is 1 (`*` 1)
  * `Z` is 2 (`*` 1)
  * `S n` is 3 (actually 3 `*` 1)

So we have a (noncommutative?) monoid `Prim*`.

The check bases on _relative prime_-ness pointwise. The check must be performed for all pairwise combinations of the case legs, for more arguments we need monoid concatenation.

_Aside: should these primes enter into the Iceberg?_

_Aside: what when the latter arguments are depedent? Fibrations?_

## At the bottom of page 5 ##

They resort to the same technique as Ahn and Sheard with _nax_: `…deriving fixpoint Nat`.

## Page 8 ##

This very much reminds me of the Iceberg!

> A desciption label ‹l› is a list starting with the name of the datatype … and followed by the parameters of that datatype.


Can we build telescopes using `do` notation? I guess so. Do we need PHOAS or can we employ the Hamana method (walking the graph)?

# Constructor Singletons #

```
data family Sing1 (r :: q) (a :: k) :: q -> *
```

This means we can have a singleton constructor and need not commit to the payload.

## Singleton Patterns ##

Can we have a primitive (like `sing`) that builds up a matcher function

```
class SingF (a :: k) where
  singMatcher :: Sing b -> Maybe (a :~: b)
```

Possibly with decidable equality?

# Forcing Inductive/Coinductive Types #

Consider this List-like GADT
```
data List :: Boolean -> * -> * where
  Nil :: List True t
  Cons :: t -> List i t -> List i t
```

`List True t` is clearly inductive, but is `List False t` possible and does it mean a properly _coinductive_ type?

Thought occurred while reading http://golem.ph.utexas.edu/category/2013/02/presentations_and_representati.html

# Mightier Monads #

A standard monad just gives you the Kleisli category. When one wants to track more invariants one can
  * use overloaded syntax for `do`, or
  * capture all extra semantics in an (adapter) thrist and compile (`foldThrist`) it to a standard monad (with extra semantics `Hidden`).

The charm of the latter way is that the hidden part can still be observed. (I was watching http://vimeo.com/61646976).

# Algebraic Effects and Handlers (for proof assistants) #

Andrej's lecture at IAS ([video](http://video.ias.edu/univalent/1213/0321-AndrejBauer)). He describes his system (based on [eff](http://math.andrej.com/eff/)) for proof assistants. Handlers have dynamic extent. (In Haskell one would implement them as implicit parameters).

operations are P x Type -> Set.

Example: `if` is a ternary operation, so the argument space is indexed by `Fin 3`. So (schematically)
```
data family If (arg :: Fin 3) :: *
data instance If 0 = Bool
data instance If 1 = a
data instance If 2 = a
```
The handlers may ask expressions (of algebraic effects) about their enclosed arguments, e.g.
```
let cond = ask 0 expr in
let cond' = eval cond in
if cond' then { let consequent = ask 1 expr; eval consequent ... }
       else { let other = ask 2 expr; eval other ... }
```
`ask` is then continuation invocation, and the type of it is `ask If :: Fin n -> *`, a dependent type.

In TH we could produce the algebraic effected expression as `[eff|if False then 3 else 42|]`
which should lift that expr up the type level and return the corresponding singleton.

The evaluator would have a bunch of `ask` handlers in dynamic scope
as well as an `eval` handler.

The concept of accessing the arguments by some arbitrary index allow for keyword arguments and infinitary arguments.

Edwin Brady [seems to like the idea too](http://edwinb.wordpress.com/2013/03/28/programming-and-reasoning-with-algebraic-effects-and-dependent-types/).

# Order Preserving Embeddings (OPE) #

The category of finite sets on N and order preserving embeddings:

http://www.cs.ut.ee/~varmo/tday-kaariku/chapman-slides.pdf

Very neat idea, and funny that I am trying to do something like this with opetopes. I.e. skip certain parts but only stretch up to a certain point.

# Mezzo preprint (of ICFP '13 paper) #

http://gallium.inria.fr/~fpottier/publis/pottier-protzenko-mezzo.pdf

This reminded me of the thread shape typing (thr :: FrameKind) for tracking resources and transfer. Not sure whether I have written down thread shapes anywhere, but the idea is to represent each thread's execution trace as `thr shape` where `shape` is fringe-like as the program executes, and `thr` is thread-specific, with primitives for forking etc.

Now resources obtain a thread-specific fingerprint, and can only be _dereferenced_ to a regular haskell value in that context, and furthermore this must be linear.

# Extended Initiality for Typed Abstract Syntax #

http://arxiv.org/pdf/1107.4751.pdf

This is building on the work of Zsidó, and is somewhat different from Fiore/Hamana.

Video about [categorical certification](http://video.ias.edu/math/stpm2012/). Faithful (semantics-preserving) translation of languages.

Given time, I should read these too:
  * http://arxiv.org/pdf/1107.5252.pdf and [as an older preprint](http://math.unice.fr/~ahrens/publications/MSCS_2012_Ahrens.pdf)
  * http://www.tcs.ifi.lmu.de/mitarbeiter/martin-hofmann/pdfs/reduction-freenormalisationforapolymorphicsystem.pdf
  * and all these [results from a query](http://www.google.de/search?rls=en&q=Andre+Hirschowitz+Monad+morphism&ie=UTF-8&oe=UTF-8&gws_rd=cr&ei=yJmbUpLEKcfbswaN5IGQCw)

# Tagless and Typeful NbE using GADTs #

Danvy et al. implement `Rep` for types, and signatures for reification, and show that all is type safe.

They mention Abel et al. as the "Dependent-Types" camp. See https://code.google.com/p/omega/source/browse/trunk/tests/NBE_lambda2.prg.

They show how a `printf` partial evaluator can be built on top of this.

# A Categorical Theory of Patches #

very cool: http://arxiv.org/abs/1311.3903

# Type inference by abstract rewriting #

Stump et al. http://arxiv.org/pdf/1211.0865.pdf
Discusses various meta-theoretic properties. Contains references to the initial technique.

# Contextual Categories #

Lots of good stuff here: https://uf-ias-2012.wikispaces.com/Semantics+of+type+theory

# Blog Posts on Type-level Magic #

  * http://ocharles.org.uk/blog/posts/2014-05-28-pure-batched-queries.html
  * https://github.com/mikeizbicki/typeparams#the-typeparams-library
  * http://www.timphilipwilliams.com/posts/2014-06-05-map-comprehensions.html
  * http://www.jonmsterling.com/posts/2012-11-10-faking-it-with-style.html

# Entropy in Biology #

http://johncarlosbaez.wordpress.com/2013/11/02/entropy-and-information-in-biological-systems/

I always said that "The road to intelligence leads through entropy."

Newer developments: https://plus.google.com/117663015413546257905/posts/icqQ6smt5yp

# STG Machine #

http://www.reddit.com/r/haskell/comments/2kswnp/the_guts_of_a_spineless_machine/

# Coinductive Reasoning #

http://jozefg.bitbucket.org/posts/2015-07-17-conats-for-cheap.html