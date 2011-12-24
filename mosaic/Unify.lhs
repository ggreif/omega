> {-# LANGUAGE GADTs, KindSignatures, StandaloneDeriving, TypeFamilies
>            , MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}

> module Unify where

> import TypeMachinery

We have an underlying data model, which consists
of
 o- n-ary constructors (here untyped)
 o- application
 o- shared or cyclic references

See Hamana's paper on "Initial Algebra Semantics for Cyclic Sharing Structures"

Short summary: even unconstrained directed graphs have
               a 'search tree'. Cycles can be introduced
               by pointers going back towards the root
               and sharing by additionally going some more
               path towards a leaf.

All in all, we assume a rooted graph with at most binary nodes
that was traversed depth-first (inorder) resulting in a binary
search tree. The first occurrence of each distinct constructor
appears on the left branch of an application, all other apparences
of it become pointers to this one.

Pointers consist of a tuple (which is reflected in the type) of
the (at least) one step up in the tree and (empty or starting
with left) path to the actual node. These paths may never address
pointers (pointers are not addressable) and the traversal makes
guarantees that this never ever becomes necessary.

See also purgatory/LambdaPath.omg for insights.

Anyway, we want a kind for the shape and a kind for the
path from root so we can address any relevant (non-pointer)
node.

kind Overlying -- shape of Underlying
--TODO--

kind Turns -- the way to descend

> data Root; data A1 p; data A2 p; data Here

We also would like to exclude non-addressable nodes
kind Whether = Yes | No

> data Yes; data No

kind Addressable :: Whether -> *1 where { Target :: Addressable Yes; Miss :: Addressable No }
--TODO--

> data Target; data Miss

            Arity ---+    +---- Path to here
                     v    v

> data Underlying :: * -> * -> * where
>   App :: Underlying (S a) (A1 r) -> Underlying n (A2 r) -> Underlying a r
>   Ctor :: Nat' n -> Underlying n here
>   Pntr :: InTree (S up) here => Nat' (S up) -> Path p -> Underlying noArity here
> deriving instance Show (Underlying a p)

We actually need a third parameter, the tree shape. I prefer not to
additionally model it right now.

Above we compute the Arity and the effective Address of a pointer.
Here come the type functions how it is done.

> class InTree up path
> instance InTree Z path
> instance InTree up path => InTree (S up) (A1 path)
> instance InTree up path => InTree (S up) (A2 path)

> type family EffPath a n r :: *
> type instance EffPath (A1 a) (S n) r = EffPath a n r
> type instance EffPath (A2 a) (S n) r = EffPath a n r
> type instance EffPath a Z Here = a
> type instance EffPath a Z (A1 r) = A1 (EffPath a Z r)
> type instance EffPath a Z (A2 r) = A2 (EffPath a Z r)


Please note that constructors do not have names, they have
positions (addresses) in the tree. We refer to the same constructor
by sharing. A constructor in a different position is a distinct
one and they cannot unify.

We should also have holes, corresponding to unification variables. --TODO--

Now the Path type is still missing. Here we go:

> data Path p where
>   Root :: Path Root
>   Here :: Path Here
>   A1 :: Path p -> Path (A1 p)
>   A2 :: Path p -> Path (A2 p)
> deriving instance Show (Path p)

> grab :: Path here -> Path p -> Underlying a here -> Sub p
> grab Root Root tree = Sub tree
> grab here p (Pntr (S n) rel) = Chase n rel
> grab here (A1 p) tree = case grab here p tree of
>                         --Sub (l `App` _) -> Sub l
>                         --Sub (Pntr Z Root) -> undefined -- Redirected (A1 p) tree -- Sub tree
>                         _ -> Miss
> grab here (A2 p) tree@(App _ r) = case grab (A2 here) p r of
>                                   Chase Z Here -> Redirected here tree
>                                   Chase (S go) p -> Chase go p
>                                   Chase Z p -> undefined --case grab' here p tree of
>                                                     --a -> a
>                                   Sub t -> undefined --Sub t
>                                   _ -> Miss
> 

> data Sub p where
>   Miss :: Sub p
>   Sub :: Underlying a p -> Sub p
>   Chase :: Nat' n -> Path pth -> Sub p
>   Redirected :: Path pth -> Underlying a pth -> Sub p
> deriving instance Show (Sub p)

> t0 = Ctor (S Z) `App` (Ctor (S Z) `App` Pntr (S Z) (A1 Here))
> t1 = grab Root (A1 $ A2 Root) t0
> t2 = grab Root (A2 $ A2 Root) t0
