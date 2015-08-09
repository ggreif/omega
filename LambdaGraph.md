# The Name #

[Ariola's work](http://ix.cs.uoregon.edu/~ariola/cycles.pdf) contains an early mention of the _lambda-graph_. It remains to be seen whether my treatment of `letprec` is different/better and how.

Recent research uses TermGraph as the name: http://arxiv.org/pdf/1401.1460.pdf

There is a [nice animation of termgraphs](http://www.cas.mcmaster.ca/~kahl/HOPS/ANIM/index.html) too.

Classical paper on termgraphs (http://citeseer.ist.psu.edu/viewdoc/summary?doi=10.1.1.42.8384)

See also Thorsten Wißmann's project thesis on rational fixpoints in nominal sets.

Peter Selinger [on lambda algebras](http://www.mscs.dal.ca/~selinger/papers/combinatory.pdf).

# Main Idea #

A graph representing (extended) lambda calculus terms is transformed into a _search tree_ and sharing, cycles, etc. are represented by (up`*`{down|left|right}`*`) references.

![https://omega.googlecode.com/svn/wiki/LambdaGraph.svg](https://omega.googlecode.com/svn/wiki/LambdaGraph.svg)

Key document: http://arxiv.org/pdf/1007.4266.pdf, but see also http://www.cs.gunma-u.ac.jp/~hamana/Papers/poly.pdf

I started implementing it here: https://code.google.com/p/omega/source/browse/mosaic/LambdaBuilder.hs

Some relevant packages:
  * http://hackage.haskell.org/package/compdata
  * http://hackage.haskell.org/package/regular
  * http://hackage.haskell.org/package/multirec

Some provide PHOAS-based finitely representable graphs.


# How it works #

... open up Adam Gundry's thesis ...

Each _lambda node_ is a portal where subgraphs are passed in by means of _application nodes_. Reference nodes (usually) point to one of these portals and mean: the subgraph that entered there. When a reference points to a non-binder, interesting semantics may arise, such as sharing, cycles etc.

## well-formed graphs ##

All references of the (full) graph are pointing at some node of the graph. When in the process of zipping, we have a partial graph in its surroundings, and each reference must be resolvable into either the partial graph or the surroundings.

## canonical references ##

References are canonical when they only point upwards. Binding references are canonical ones that point at lambda nodes. When all references in a (sub)graph are canonical, then the (sub)graph is canonical.

## `let` expressions ##

These are non-canonical graphs. When a reference ascends to an application node and descends to the left into a lambda node.

![https://omega.googlecode.com/svn/wiki/Letrec.svg](https://omega.googlecode.com/svn/wiki/Letrec.svg)

`(λ{up}) @ {up.left`}

corresponds to (recursive) `let a = a in a`

_Note: the middle_ `a` _corresponds to the right branch of the application node._

## search tree ##

When the graph is either canonical, or all references have some `up` segments followed by a `left` segment. The rest is not relevant, but may not contain `up` segments.

All _previously mentioned_ subgraphs can be accessed this way. The search tree configuration thus is the most generic one, offering maximal sharing.


# Substitution #

Beta reduction happens by lifting the right application branch up a level, the left one up two levels, and than recursively inserting the pushed down right branch in the appropriate reference nodes of the left branch.

We need primitive movements (_steps_) for this.

## Step: `Down`, `Left`, `Right` ##

These are easy. Mark a _limit node_ and a _target node_ below it. Everything outside the cone of the former counts as the environment and references that point into the environment are _free_. These stretch.
Everything else remains the same.

TODO: illustrate

## Step: `Up` ##

This is hairy. Similarly we have our limit node and the target node in its cone. Free references are simply shortened by removing the initial `Up`. References that point into the cone of the target node do not change. Otherwise, ... (TODO: I need to think about this.)

## Movements ##

A coherent sequence of steps is a _movement_. These form a category.

Since primitive movements only affect _free references_ (those into the context) stream fusion like techniques could be applied to avoid multiple traversals of the tree.

## Improvements ##

  * Get rid of `Down`, use `Right` instead.

  * Have splits as steps. A split is an expression (in terms of the current location) used to decompose a pattern: `a@(Cons head tail)` which establishes an equivalence relation between the two sides of the `@`, and is used to introduce bindings for parts of values.

### How does splitting combine with `letrec`? ###

The interactions may be non-trivial. Can we obtain copatterns? Can we have `a@(S a)`?

# Notes #

There is only one binder (in the spirit of [Kamareddine, JFP 2005](http://journals.cambridge.org/action/displayAbstract?fromPage=online&aid=331521)) and by resorting to level inference, it can be recovered whether it is a ∏, λ or Λ.

Later there will be a ∑-like binder too. (Actually, ∑ is the same thing as ∏, only being _uncurried_, i.e. it has moved [into the pattern](HomologyTypes#Connection_between_Pi_and_Sigma_binders.md)).

The application node could come equipped with a natural number, signifying the number of iterated applications, i.e. S<sup>n</sup>Z, for constant `n`. Fixpoints can also be encoded by f @ {up}. In this case
non-zero `n` would collapse to `1`, and for `n=1` it would be a common loop.

So an application node with `n=0` would normally be eliminable, unless there are {up.left} etc. references in the right subgraph.

Iterated nodes are useful for finitary sharing, as type checking etc., can process the many iterations in bulk.

# Types #

This is the most important thing. We have to ask where the types appear in this scheme. One could suggest that a type is living _above_ each of those nodes, forming a similar graph of nodes (albeit simpler), like this:

TODO: illustration

In the first floor above the the λ subtree there is a congruent ∏ subtree, etc.

_But this view of the world is wrong!_

The types live on the connections between the nodes, a λ _pushing_ its ∏ type (which is indeed derived from the subtree shape) up towards applications, the application in turn pushing some (a -> b) in opposite direction. Identifications of nodes induce identifications of pressure frontiers. The two connection points of the connections constitute two views (aspects) of the _same type_ with the line representing the equation (constraint). However there are inference systems (e.g. OutsideIn) which inhibit information flowing outward from certain places. A constraint solver just needs to read off the equations and arrange for a solution, iterating into higher dimensions.

## Type annotations ##

Remains to clarify how types enter into the graph. For that we need an annotation mechanism, but we do not intend to add new flavors of nodes.

So what we can do is to _apply_ an annotation by _apply nodes_:
```
({::-ann} @ <expr> @ <type>)
```

`::-ann` would become _the_ level spanning relation. Of course these may appear in left (pattern) and right-hand sides too.

# More Interesting Papers #

http://gallium.inria.fr/~balabons/Recherche/Balabonski-ICFP13.pdf mentions the "sharing-via-labelling" technique.

Names for Free [with commentary](http://ezyang.tumblr.com/post/62061779275/haskell-names-for-free-polymorphic-views-of-names-and). Note the ∑-∏ isomorphism he gives.

## Some older papers in ESOP 2000 proceedings ##

Sharing Continuations: Proofnets for Languages with Explicit Control
by Lawall and Mairson

Improving the Representation of Infinite Trees to Deal with Sets of Trees
by Mauborgne

# Extensions #

Suppose we want to compare/unify two such graphs. Naturally, we'd put two search trees on top, and recursively walk down, comparing leaves, and nodes.

Clearly, references encoding the same path unify, as do variables. Applications unify when some (non-normal) reduct - this should be nondeterministic reduction - unifies.

But when two on-top variables unify, and we integrate the lhs and rhs graphs after the successful unification into a common graph, we have to be careful not to keep both variables around. Instead make a top-to-bottom reference.

I am tempted to introduce a unification node (besides application nodes) to record successful (past) unifications. Reference paths crossing through unification nodes are then the eliminated variables. May we  consider the unifications as local gluings of "continents" and have something like a sheaf, that describes the globality of our program? The only reference to "unification" and "sheaf" that I found is http://arxiv.org/pdf/1403.3351.pdf

NB.: This seems to rhyme well with "equality types" of MLTT, where these are needed as a primitive.

NB.: HoTT defines higher inductive types (data constructors have types as unification nodes). Can we neatly model this? Maybe we do not need unification nodes, just splitting patterns, as the concepts are pretty much identical.

NB.: using splitting moves can we reduce the exponential complexity of inference for `id id id id id id ...`?

NB.: One could track intermediate reduction steps of the normalization process as on-top graphs connected by unification nodes.

NB.: The defining equations of functional programs correspond to application nodes (e.g. `letrec`, context extension). Can unification nodes play this role too? How big is the overlap?