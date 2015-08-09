There are many terms that you come across when reading the Ωmega sources, where you'll stop and scratch your head about what they mean and why they are used. This page is intended to be an alphabetic glossary of those terms with motivation how to use them.

An important source of wisdom is also [the GHC commentary](http://darcs.haskell.org/ghc/docs/comm/), as Ωmega owes much to that project in terms of implementation guidance and concepts.

# Freshness #

Freshness is an important concept when dealing with _sharing_ in the internal representation. For example constants can always be shared, but when it comes to bindable entities (like type variables etc.) any performed bindings amount to a specialization of the original data and thus (before and after) are not semantically equivalent any more.

Since bindings are (usually) tracked with an auxiliary map, a parametrized type cannot be included in a new type twice with differing parameters unless it gets freshened before each parametrization. The process of replacing the names of formals before a performed binding with a fresh set of names is called _freshening_ and the overall concept is called _freshness_.

# Rank-N #



# Zonking #

Tree-like entities that contain writable references (which usually get filled-in by a unification-like process) are _zonked_ by elimination of all references that are already filled-in. This happens in a monad that can dereference, and is basically a tree traversal that results in a copy.
Usually before two trees are unified, both trees must be zonked, so that references do not get overwritten in theoriginals. Without zonking, the unification (and similar) algorithms must be explicitly designed to not overwrite references that are already filled-in and possibly to undo bindings when unification fails.

In the process of zonking, usually another optimization is performed, namely the short-circuiting of reference chains by a target.