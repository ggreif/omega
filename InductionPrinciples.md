# Introduction #

Each inductive datatype corresponds to some pattern functor. Interestingly these functors give rise to different induction principles. I believe that the `prop` definitions in Ωmega are closely related.

# Relevant Papers #

## Inductive Types Imply Induction Principles ##

These give rise to propositions which can be pretty elaborate:

http://homepages.inf.ed.ac.uk/als/ScottInScotland/ghani.pdf
(The [full paper](http://portal.acm.org/citation.cfm?id=1887488) corresponding to the presentation.)

The `indNat` principle  has striking similarity with
```
data Nat :: *1 where
  Z :: Nat
  S :: Nat ~> Nat
 deriving Nat(t)

prop Nat' :: Nat ~> *0 where
  Z:: Nat' Z
  S:: forall (a:: Nat) . Nat' a -> Nat' (S a)
 deriving Nat(v)
```
as defined in the Ωmega builtins. `prop` seems to project from `*` to `Prop`, the latter being the category of propositions.

See also Robert Atkey's [blog](http://personal.cis.strath.ac.uk/~raa/posts/2011-04-28-folds-and-induction.html).

## Deriving Refinements ##

Have to read this, but at first glance it tries to come up with the index types for non-indexed (G)ADTs.

http://personal.cis.strath.ac.uk/~raa/inductive-refinement.pdf

Might be interesting to see whether the ability to come up with index types means that an induction principle can be established and whether the user defined (or automatically derived) _initial algebra package_ can be proved terminating w.r.t. the induction principle (see _sized types_).

## Initial Algebra Semantics for GADTs ##

Resorting to _left Kan extensions_ allows to rewrite GADTs to _nested ADTs_. Only the `Equal` GADT and existentials are needed for obtaining something that is isomorphic to any given GADT.

http://portal.acm.org/citation.cfm?id=1328438.1328475&coll=DL&dl=GUIDE&CFID=7492414&CFTOKEN=30206845

Interestingly I have been playing around with [similar ideas](http://svn.berlios.de/svnroot/repos/al4nin/trunk/purgatory/Sum.omg?p=1038). See the `Equate` constructor of GADT `Free`.

Recently Fiore and Hamana gave an initial algebra semantics to GADTs via [polynomial functors](http://www.cl.cam.ac.uk/~mpf23/papers/Types/gadtif.pdf).

## Set- and Bag-like Theorems ##

[Issue 6](https://code.google.com/p/omega/issues/detail?id=6) describes an idea with _bagifying_ resp. _setifying_ type functions. These are suggested to be magic builtins, but there is another possibility of postulating _associativity_, _commutativity_ and _redundancy_ for list-like (or even tree-like) datatypes, with `theorem` declarations. The latter two theorem forms would correspond to _bags_, resp. _sets_, and could be implemented internally in a more efficient manner.