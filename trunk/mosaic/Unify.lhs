> {-# LANGUAGE GADTs, KindSignatures, StandaloneDeriving #-}

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

See also purgatory/LambdaPath.omg for insights.

Anyway, we want a kind for the shape and a kind for the
path from root so we can address any relevant (non-pointer)
node.

kind Overlying -- shape of Underlying
--TODO--

kind Turns -- the way to descend

> data Root; data A1 p; data A2 p; 

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
>   Pntr :: Nat' up -> Path p -> Underlying noArity notAddressable
> deriving instance Show (Underlying a p)

Please note that constructors do not have names, they have
positions (addresses) in the tree. We refer to the same constructor
by sharing. A constructor in a different position is a distinct
one and they cannot unify.

We should also have holes, corresponding to unification variables. --TODO--

Now the Path type is still missing. Here we go:

> data Path p where
>   Root :: Path Root
>   A1 :: Path p -> Path (A1 p)
>   A2 :: Path p -> Path (A2 p)
> deriving instance Show (Path p)

> grab :: Path here -> Path p -> Underlying a here -> Sub p
> grab Root Root tree = Sub tree
> {-
> grab here (A1 p) tree = case grab p tree of
>                         Sub (l `App` _) -> Sub l
>                         _ -> Miss
> grab here (A2 p) tree = case grab (A2p tree of
>                         Sub (_ `App` r) -> Sub r
>                         _ -> Miss
> -}

> data Sub p where
>   Miss :: Sub p
>   Sub :: Underlying a p -> Sub p
> deriving instance Show (Sub p)
