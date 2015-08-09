# Introduction #

_Note: I guess all what I believe is my ideas are actually old hats._

Each unconstrained (but otherwise typed) logical variable grows a complete guess tree in that position. (I assume inductively defined types.) The guess tree again grows at each recursive position of it.

When we have some constraints (such as instantiated type params/indices) some branches of the guess tree are moot, no need to generate them.

Each node has a distance from the logic var. This distance should determine the speed of newly generated guesses.

We could use a parallel writer monad for depositing (distance, node) pairs, with a continuation that is invoked to go deeper. Possibly, we could write the path to the node (depth calculable).

The generated nodes would go in a multiset.

How to be sure that we have all (eligible) guesses of a certain depth?

Why inductively sequential? Is there _converse_ of the type function? Need it be inductively sequential?
Is the (,)-thrist (category of relations) of any use?

Can we build a narrower from _class Data_ definitions (or similar IcebergTypes defs)?

# Reading List #

LogicT
http://www.cs.rutgers.edu/~ccshan/logicprog/LogicT-icfp2005.pdf

Implementing Functional Logic Languages Using Multiple Threads and Stores
http://web.cecs.pdx.edu/~apt/icfp04.pdf