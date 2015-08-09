[
At this stage all I have is this concept draft. Please do not pass on to other
without asking me first. I would like to present something more coherent
to a wider audience.
]

[
would this fit into Journal of Functional Programming (JFP) ?
What else?
]

---

# Pi-Sigma: A Topological Vision #

_A scenic journey through the world of pure type systems_

## Abstract ##

We present a visual canon for the strongly typed dependent
lambda calculus that is both expressive and appealing,
showing a colorful aspect of the highly abstract mathematics
behind it. The introduced entities will be given concrete forms
so that understanding can be obtained even with less than
stellar levels of devotion to the subject. The exhibited plasticity
and orientation of the objects serve the purpose of apprehension
and memorability.

## Intro ##

As computer science and real-world software installations are increasingly under pressure from security exploits, the necessity to harden software products, by proving their concordance with the specification, arises. The academical advances in the area of understanding and embracing sophisticated typing systems is starting to trickle into the practice of day-to-day programming. The last forty years have shown that the solutions offered by type systems represent all the mathematical rigor needed to make programs safe.

In this educational pearl we set out to give forms to the abstract terms appearing in the typed formalisms and make suggestive pictures how a programmer can think about them and mentally connect the parts.

We shall examine a type system not unlike to the programming language [Ωmega](http://code.google.com/p/omega), its particulars and the ideas behind it.


### Typed lambda calculi ###
its terms and types
  * vars: x, y
  * application: (x y)
  * value abstraction \x.y; value pairing <x,y>
  * <wiki:gadget url="http://mathml-gadget.googlecode.com/svn/trunk/ascii-gadget.xml" border="0" up\_content="type abstraction `prod\_(x text(::)D)R(x)`, type pairing `sum\_(x text(::)T)U(x)`" height="35"/>

A little explanation to our nomenclature is due now. In most publications the domain and range of dependent products is written behind the product symbol, separated by dots. We put the domain under the product symbol and the range after it. Similarly for the pairing datatypes (dependent sums). When the range (resp. the second pair component) does not actually depend on the domain's name we will often omit the name part. This case is usually written as function type D->R (resp. pair (T, U)) in the literature.

### Omega ###

Omega provides an infinite hierarchy of types

![http://omega.googlecode.com/svn/wiki/Kind-hierarchy.svg](http://omega.googlecode.com/svn/wiki/Kind-hierarchy.svg)

where each level below is typed by the level above as highlighted by the arrows.


### Classical interpretation of types ###

as sets

  * 42 ∈ ℤ
  * Int ∈ `*`

### Type theory interpretation ###

This is also called the Curry-Howard correspondence

(logic) types as propositions, values as proofs

  * `\x.x` proves `Int -> Int`
  * 42 proves `Int`
  * `Int` proves `*`
  * `Eq` proves `Equal Int Int`

The first three are not a big deal, but the last is interesting.

### Coloring our Ideas ###

The standard (string diagram) representation of a function
is like this:

![http://omega.googlecode.com/svn/wiki/Arrow-f.svg](http://omega.googlecode.com/svn/wiki/Arrow-f.svg)

Let's assume `f = \ a -> not (not a)`, the identity function on booleans.
But we are much more interested in the type of the value f. The
dependent lambda calculus assigns a type ∏x:Bool.Bool to it,

∏x:Bool.Bool<wiki:gadget url="http://mathml-gadget.googlecode.com/svn/trunk/mathml-gadget.xml" border="0" up\_content='prod\_(tttext(Bool))tttext(Bool)' height="15"/> corresponds to

![http://omega.googlecode.com/svn/wiki/Bool-cones.svg](http://omega.googlecode.com/svn/wiki/Bool-cones.svg)

two cones inside-out: `Bool -> Bool`.
We use colours to differentiate between the two sides of the surfaces. The figure shows how the ∏ combinator reverses 'inside' and 'outside'. This is the consequence of the well known contravariance of function types.

[
we could use Rational numbers too, with contravariance resulting in reciprocity, but then our picture would be less lively
]
[
Klein bottle when pasted with IxS1, what when pasted with S0xB1?
]

We live in [one-point compactified?] 3-dimensional space: there is only 1 kind: **(and on the other side the same) [this the projective space?](is.md)**

We need a small 'black hole' around the point where the self-intersection happens, because the 'implementation' of the function type is not available for inspection (existential). [this be the case for the function value, or the type? Value sounds better](should.md)

## Types are Topological Objects ##

manyfolds

### Our interpretation of types ###

(topology)

42 is boundary of `Int`

`Equal Int Int` is boundary of `*`


### The Simplicial Complex ###

  * 0-dimensional entities: (pointlike) combinators (named), constructors are shown as dense sets whose

  * 1-dimensional entities: Values

  * Surfaces: types (colored on the sides)

  * Volumes: kinds (e.g. type of gas filling it)

We will see that the zero-dimensional entities are the most crucial ones, as they are the connecting point for
> - values -- y = f(x) -- x travels on the cone towards combinator f and y leaves on the result cone.
> - types -- the incoming cone and result cone touch in the focal point, the combinator
> - kinds -- `*`, `* ~> *`, etc. -- the volume enclosed in the cones

Values being loops travelling on (type) surfaces is seemingly an arbitrary choice, why not points (or a discrete set of them) travelling on something one-dimensional? After all, `42` seems very point-like. Two reasons:
  * as said above 0-dimensional objects are already taken
  * points are too devoid of structure to use them for something of utility
A nice analogy to string theory arises here. Point-like particles cause problems, which go away (to some big extent) when increasing the dimension by one.

#### Topology redux ####

smooth manifolds

deformability

singularities

homotopy

homology (interested in cycles that are not boundaries), bordism

classes, representants

### Homology and the Algebra of Datatypes ###

From each type an algebraic structure can be distilled. This is the signature functor, having some polynomial-like properties. What is lost in the process are the names of types, constructors and the order of elements in tuples as well as exponentials. After all these objects are all modulo isomorphism.

There is another [similar distilling process](http://en.wikipedia.org/wiki/Simplicial_homology), going from simplicial sets to modules over some ring. This is another lossy functor. But ∂∂ = 0. This admits exactness, but it becomes interesting where exactness is broken. H<sub>n</sub>(X, X0) is ker∂<sub>n</sub> / im ∂<sub>n+1</sub>. H<sub>n</sub> exposes the generators of our geometry as module dimensions which are not trivial. A torus has two of them: Z+Z. Compare this to Bool = 1+1.

So the basic idea is to find surfaces which are the coimages of the data type's signature under some homology-like functor. The rest is to paint the coimage with pretty colors to account for the lost information.

Videos about [Homology](http://video.ias.edu/univalent/1213/0306-EricFinster). Video from [LHUG (Algebra of Datatypes)](https://www.youtube.com/watch?feature=player_embedded&v=YScIPA8RbVE#!).

### The Nat Datatype ###

The usual definition of natural numbers is
```
data Nat = Zero | Successor Nat
```

We can assign some images to these data constructors:
  * Zero:
    * as a type — a (topologically open) unit disc with yellow on one side and green on the other;
    * as a value — the unit circle (S1). [S1 is the same as the Zero∧Zero when those cover a S2 (sphere)](The.md)

  * Successor:
    * as a value — a function with arity one
    * as a type — two cones meeting in the middle, one to the left (the argument type) and one to the right (the result type). The result cone flips the inside and outside colors and softens the hue of the colors (but any other progressive - i.e. 2-forward, one back - coloring scheme is feasible).

> Typing relation: _Boundary_ :: _Manifold_

this can happen at any level

We get a homology theory when we have

∅ :: Values :: Types :: Kinds :: Sorts :: ⋯
> ← ∂ ―

[we have to define a Value/Type/etc. at each level as a 'triad' (X; X0, X1)](actually.md)
[Mayer-Vietoris sequences?] [Update 2014-11-12](http://www.qmac.ox.ac.uk/events/Talk%20slides/Evan%20Cavallo.pdf)

!!! tau thrists, higher degrees, de Bruijn

in our pure type system below we have infinite levels (see below)

[
Pulling the colors from the mandelbrot set?
using gases and flexible membranes to visualize (cones, spheres, ellipsoids, paraboloids, hyperboloids)
depends on the type of gas inside
]

### Definitions/Uses and sharing ###

We speak of the 'same value' (and at higher levels 'same type' same, 'same kind', etc.) if there is a bordism [old parlance cobordism](in.md)
which connects the manifolds at the same level. I.e. the lambda calculus term (let a = 5 in (a, a)) [we want to write this with S-K combinators? -- NOT](do.md) contains a bordism between the 5 and the two mentions of a. [we have a bordism with homotopy-equivalent boundaries, we can still say the value is used linearly.](When.md)

So definitions allow sharing.

[My idea is that values of a singleton type can be 'shared' indefinitely, since there is only one member of the type anyway.
This might be very interesting for the Equal type with its intensional proof machinery]

### Pairs (Sigma) ###

We have already seen the pairing combinator in action above, we still have to picture the corresponding type ∑x::A.B.

Let's revisit the values first. These are tori. The first generator is by `A` and the second by `B` (which can depend on parts of `A`), making it a fiber over a value `a :: A`.

TODO: Add picture. Also disjunctions (E.g. `Maybe`)
TODO: Spin 1/12 object depicting the dependency between hands of a clock.

The topologically interesting things happen in codimension 1 (and 2). See Poincaré-duality.

Now, how can the types look like? x::A says that x is a boundary of A, and each of these (potentially) reveal a type surface B. If the pair exists and we extract x than we know that there is a type surface determined by x whose boundary is y::B(x).

### Constructors ###

Constructors appear at every level, and contrary to functions (at any level) they do not transform information
but accumulate/aggregate it [accumulate: may contain existentials whose type is not visible outside. Usually the values
themselves are existential, though.]

We depict value constructors like a mushroom. The inner bubble joined on the top of a cylinder with a bigger bubble joining at the same place. The circle where everything joins is a dense set (compact) and its closure homeomorphic to a value. The dense set is still 0-dimensional [no value can pass through it](thus.md).

Type constructors are harder to depict, as they join solids instead of surfaces, so the dense set that joins them has
a 2-dimensional closure. We could place a B3 inside, and a hollow ball outside (the latter being **~>**). [this idiom
works well for unary type constructors, but not for n-ary ones :-(  we need shrinking balls in time to get it right.]

[we say that constructors are just functions (i.e. one point)?; but then we lose the nice mushroom meme.](could.md)

#### pattern matching ####

Pattern matching is just the opposite of aggregation, anything new here?

### Quantifiers ###

!!!TO BE TOLD

#### Universal quantification ####



#### Existential quantification ####

black hole (no information can leave it)
each black hole has its own category, namely
the location of the quantifier and when it got
instantiated. Corresponding functions must
be instantiated from the same category, otherwise
they are not unifiable.

[existential types as black velvety surfaces?](Visualizing.md)

Dependent pairs (sums), proper Sigma types.

Existentials arise when combinators are (partially)
applied, as the resulting function type does not
mention that argument any more.
Only when the combinator is opened (running the function
or pattern matching on the data structure) the hidden values
become exposed.
Even when the type is well-known the value is not immediately
fathomable, but normally it can be scrutinized.

When even the type is existential, then we have the black
holes from above.

#### Connection between Pi and Sigma binders ####

The connection is currying:

  * non-dependent: A -> (B -> C) == (A, B) -> C
  * dependent: a::A -> (b::B(a) -> C(a,b)) vs. (a::A, b::B(a)) -> C(a, b)

So technically, B appears on the equation's RHS, forming a partial application, or in the LHS' pattern. Same thing in cartesian closed categories.

Since (unary) constructors name a bijection between input and bound name, it is possible to regard sigma as identifying the input with the constructor application, effectively peeling off the constructor:

INPUT == ctor `<bound-name>`.
In the dependently-curried case when peeling twice this is sigma.

#### Higher ranks ####

dynamic color scheme (varying), rainbow-like
colors of cones locked together by type variables
(or equality types)

### The Identity Type ###

The identity type is one of the mightiest weapons in a typed
programmer's arsenal. The identity type can be instantiated
(at any level) with two type parameters at any level, but the
the actual identity is proven at the value level:

```
data Equal a b :: * where
  Eq :: Equal c c
```

If the programmer succeeds to obtain an `Eq` value then he has
a proof in his hands that the parameters to `Equal` are indeed
denoting the same type.

!!! I have to read more on homotopy TT's Id type, which is subtly different.
in HTT the Id type corresponds to a homotopy (path) between
the two type objects. I think it is better to consider bordism here,
since we can then present the equivalence algorithmically, by
surgery on the manifold that connects the types.

We have two levels here that are interesting
  * `Equal a b` -> type constructor with two type indices
  * the value `Eq` that witnesses the fact the two indices are bordant[/a homotopy?].
The Eq value must be recursively built up if the indices are
also complex types.


#### As a proof object showing that two types are indeed equal ####
lemmata: theorems are hidden combinators that operate in
a terminating fashion on values that represent types (kinds, etc.)

visualization?
singleton types : isomorphic on both sides of the boundary relation
what is its topology, how does it connect to the cones?

Values of singleton types are tangentric circles? When is a boundary
isomorphic to a surface? [Answer: triads of Sn]
Perhaps polygons, i.e. singularities encode the type?

Homotopies.

### Definitions ###

these are simply naming the homotopy class (and a base boundary?)
all mentions of the names are connected by identity types.

[
(a :: X) = v
can we say that a little X0 ∧ X1 is embracing the type surface and thus
defining the bordism? (equivalence class)
]

i.e. in Haskell

type To a = () -> a

'To' becomes what?

type String = [Char](Char.md)

asserts a bordism between two types
but no homotopy (the names may appear
in may places (e.g. String -> String), so no
linearity is required here. BUT we need
homotopy between the disjoint components
of the boundary of the bordism.


### Dualities ###

#### Pi ↔ Sigma duality ####

Depending on the viewpoint we have
> o two joined cones
> o opposite cones

#### Existential ↔ Universal ####

calling universally quantified function of arity 2 is
> - creating a copy of the still uncolored function (as value - a double-circle on the left single on the right, probably with 3 lines to the focus?)
> - it has two nested cones to the left, the inner one is joined with the first argument, which colors that cone on the inside and the outside
> - the second cone is filled the same way, colours it
> - big bang: value(s) now wander to the focal point, in this combinator (singularity) they get processed according to the combinator's inner rules and the result leaves through the right cone, coloring the surface in the process.

from inside of the combinator
> - combinator internal machinery is invoked when the function is fully saturated
> - from internal perspective there is a circle for each argument
> - type of each quantified argument is purely existential, unless type also occurs in the result cone
> - reduction rules are applied, until the last combinator
> - combinator (the point) disappears

#### Polarity, co-/contravariance ####

covariance: colors not flipped
contravariance: colors flipped

##### Fixpoints of types #####

We lose the variance, it becomes both colors at the same type.
As if we pasted a moebius strip into a disk-shaped hole of the surface.

#### Inside-outside duality ####

Speculative!
when we are in the projective plane there is no inside or outside
but in normal space


### Type inference, Unification ###

+++ inference rules, proof objects
+++ bidirectionality
+++ infinite manifolds (values: non-termination, types: infinities by unification)
+++ termination (sized types)

(\x.x x) (\x.x x)
not typable -> moebius? Two colors not separatable?

Is unification the process of verifying homotopies (of types)?
What about type variables? Are Eq values just the inhabitants
of (Equal a a) and together with transitivity allowing the path to extend?

### Conor's derivatives of datatypes ###

Speculative: can we visualize the holes in the types?
The holes introduce new boundaries. [I have a little sketch
at work.]

## Dependent types ##

### Pure type systems ###

### smart quantifiers: telescopes ###
relating several levels

### "Pi in the Sky" Programming ###

directly below **∞
> - there is only one namespace, types and 'values' (their boundaries) appear at the same level (actually they are isomorphic)
> - the (::) typing relation is still possible
> - Z < Nat > S n, subtyping, `Z :: Z`, `S n :: S n`, `S :: S` [??? how can we show this, topologically? Simple: Mayer-Vietoris of tori
with genus n]**

## Other Work ##

Has somebody already embarked on visualizing (and/or topologizing) the lambda calculus?
[yes, I have seen an animation of the (\a.aa)(\a.aa) reduction as a repetitive deformation]

Visual canons in
  * (molecular) [chemistry](http://arxiv.org/ftp/arxiv/papers/1307/1307.6360.pdf)
  * visual notations (UML?)
  * electrical engineering (scematics, TMS74xxx digital circuits)

Diagrams of moving 'particles/waves' in [negative and reciprocal types](https://www.cs.indiana.edu/~sabry/papers/rational.pdf).

Feynman diagrams. (Strings, Worldsheet)

Operads
  * in FRP, signals, boxes, [wiring diagrams](http://math.mit.edu/~dspivak/informatics/talks/CMU2014-01-23.pdf)
  * [Feynman categories](http://video.ias.edu/pisgs/2013/1206-RalphKaufmann)

Opetopes
  * [Long(-ish) introduction](http://arxiv.org/pdf/0706.1033.pdf)
  * [Interactive editor](http://sma.epfl.ch/~finster/opetope/opetope.html)
  * [Opetopes slides](http://sma.epfl.ch/~finster/opetope/types-and-opetopes.pdf)
  * [along with some commentary](http://golem.ph.utexas.edu/category/2012/06/directed_homotopy_type_theory.html#c041675)
  * video IAS [Higher Dimensional Syntax](http://video.ias.edu/math/stpm2012/finster)
    * [PDF](http://uf-ias-2012.wikispaces.com/file/view/Higher-Dimensional-Syntax-Slides-Finster.pdf)
  * video IAS [The Calculus of Opetopes](http://video.ias.edu/1213/univalent/0131-EricFinster)
    * 35:18 → level polymorphism
    * _universal cell_ same as commutative diagram, coercion witness, (directed) identity typed value
    * opetope: string diagram, pasting diagram, diagram category object

### n-Categories, string diagrams ###

[Tangles, diagrams and monads](http://vimeo.com/6590617) by Dan Piponi

Gooseflesh paper: http://arxiv.org/pdf/1408.5028.pdf

Relative monads (Altenkirch, Chapman, et al.)

### Connections to String Theory ###
> world surface of strings (particles)
  * combinators: decay events, collisions
  * topological quantum field theories http://en.wikipedia.org/wiki/Topological_quantum_field_theory

### Combinatory Logic ###


### Modal logic and Geometry ###


J. Goubault-Larrecq and É. Goubault.  On the Geometry of Intuitionistic S4 Proofs.  [Homology, Homotopy and Applications 5(2), pages 137-209, 2003.](http://projecteuclid.org/euclid.hha/1088453324)

### Homotopical Type Theory ###

See also Eric Finster's [research statement](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.173.6218) about (amongst other things) the _Goodwillie Calculus_.

## Research Question ##

HomologyTypes: have the Y combinator, create the LambdaGraph for it, and compute the Homology. Does the result imply that the term cannot be typed?

Occurs check fails, but the type is finitely representable!

## Acknowledgements ##
  * to the blender guy --> artwork (+software)
  * to the topologist (3-dim projective space)
  * to the type theorist

# Bibliography #

Awodey: Homotopy lambda calculus
Baez et al.: [Rosetta Stone](http://math.ucr.edu/home/baez/rosetta.pdf)

[How to turn a sphere inside-out](http://youtu.be/sKqt6e7EcCs) does this invalidate the contravariance (hyperboloid) construction idea?

# Appendix #

Blender models

A nice blog about [picking colors](http://devmag.org.za/2012/07/29/how-to-choose-colours-procedurally-algorithms).

... and [semantic highlighting](https://medium.com/programming-ideas-tutorial-and-experience/3a6db2743a1e).