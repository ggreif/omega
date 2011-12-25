> {-# LANGUAGE GADTs, KindSignatures, StandaloneDeriving, TypeFamilies
>            , MultiParamTypeClasses, FlexibleContexts, FlexibleInstances
>            , UndecidableInstances #-}

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

> data Ctor; data App a b; data Pntr n p

kind Turns -- the way to descend

> data Root; data A1 p; data A2 p; data Here

We also would like to exclude non-addressable nodes
kind Whether = Yes | No

> data Yes; data No

kind Addressable :: Whether -> *1 where { Target :: Addressable Yes; Miss :: Addressable No }
--TODO--

> data Target; data Miss

                          +---- Path to here
            Arity ---+    |
                     |    |    +---- Shape
                     v    v    v

> data Underlying :: * -> * -> * -> * where
>   App :: NoDangling (App s u) (App s u) => Underlying (S a) (A1 r) s -> Underlying n (A2 r) u -> Underlying a r (App s u)
>   Ctor :: Nat' n -> Underlying n here Ctor
>   Pntr :: Nat' up -> Path p -> Underlying noArity here (Pntr up p)
> deriving instance Show (Underlying a p s)

The Path in Pntr has an additional constraint that it must be Here
or start A1.

Only Apps may home Pntrs, so the constraint on Root Apps is that
all Pntrs point into some App or Ctor below (or at) Root.

> class NoDangling rootee tree
> instance NoDangling rootee Ctor
> instance (NoDangling (S rootee) l, NoDangling (S rootee) r) => NoDangling rootee (App l r)
> instance NoDangling (S rootee) (Pntr Z Here)
> instance NoDangling rootee (Pntr Z (A1 p)) => NoDangling (S rootee) (Pntr Z (A1 p))
> instance NoDangling rootee (Pntr Z (A2 p)) => NoDangling (S rootee) (Pntr Z (A2 p))
> instance NoDangling Ctor (Pntr Z Here)
> instance NoDangling (App l r) (Pntr Z Here)
> instance NoDangling l (Pntr Z p) => NoDangling (App l r) (Pntr Z (A1 p))
> instance NoDangling r (Pntr Z p) => NoDangling (App l r) (Pntr Z (A2 p))
> instance NoDangling rootee (Pntr n p) => NoDangling (S rootee) (Pntr (S n) p)

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

> instance Eq (Hidden Path) where
>   Hide p == Hide q = samePath p q

> instance Ord (Hidden Path) where
>   Hide Root `compare` Hide Root = EQ
>   Hide Here `compare` Hide Here = EQ
>   Hide Root `compare` Hide Here = LT
>   Hide Root `compare` Hide (A1 _) = LT
>   Hide Root `compare` Hide (A2 _) = LT
>   Hide Here `compare` Hide (A1 _) = LT
>   Hide Here `compare` Hide (A2 _) = LT
>   Hide (A1 _) `compare` Hide (A2 _) = LT
>   Hide (A1 m) `compare` Hide (A1 n) = Hide m `compare` Hide n
>   Hide (A2 m) `compare` Hide (A2 n) = Hide m `compare` Hide n
>   Hide _ `compare` Hide _ = GT

It is important to point out that Path will be used in
two senses, relative and absolute. The two conceptually
associate in opposite directions and have different
base atoms:

Root ) A1 ) A2 ) ... ) Ak | Ak ( ... ( A2 Here
---- absolute part ------> <------ relative part

In Omega I would use a different set of constructors
and pretty print them as LeftList and RightList.

We connect them by a type function to obtain one
absolute path (undecidable instances!).

> type family PathSum a r :: *
> type instance PathSum a Here = a
> type instance PathSum a (A1 r) = PathSum (A1 a) r
> type instance PathSum a (A2 r) = PathSum (A2 a) r

> type family PathExt r r' :: *
> type instance PathExt Here r = r
> type instance PathExt (A1 r) r' = A1 (PathExt r r')
> type instance PathExt (A2 r) r' = A2 (PathExt r r')

Grab is a function to get a subtree at a relative path

> grab :: Path here -> Path p -> Underlying a here s -> Sub (PathSum here p)
> grab here p (Pntr n rel) = Chase n rel p
> grab here Here tree = Sub tree
> grab here (A1 p) tree@(App l _) = grab' tree (A1 here) here p l
> grab here (A2 p) tree@(App _ r) = grab' tree (A2 here) here p r
> grab _ _ _ = Miss

Helper function that can chase

> grab' tree down here p r = case grab down p r of
>                            Chase Z Here Here -> Redirected here tree
>                            Chase Z pth p -> case grab here ext tree of
>                                             Sub t -> Redirected (addPath here ext) t
>                                             _ -> Miss
>                                        where ext = extendPath pth p
>                            Chase (S go) pth p -> Chase go pth p
>                            sub -> sub

Combine an absolute and a relative path to an absolute one

> addPath :: Path a -> Path r -> Path (PathSum a r)
> addPath a Here = a
> addPath a (A1 p) = addPath (A1 a) p
> addPath a (A2 p) = addPath (A2 a) p

Combine two relative paths to a longer one

> extendPath :: Path a -> Path r -> Path (PathExt a r)
> extendPath Here r = r
> extendPath (A1 r) r' = A1 (extendPath r r')
> extendPath (A2 r) r' = A2 (extendPath r r')

Are we having two equal paths?

> samePath :: Path p -> Path q -> Bool
> samePath (A1 p) (A1 q) = samePath p q
> samePath (A2 p) (A2 q) = samePath p q
> samePath Here Here = True
> samePath Root Root = True
> samePath _ _ = False

> data Sub p where
>   Miss :: Sub p
>   Sub :: Underlying a p s -> Sub p
>   Chase :: Nat' n -> Path pth -> Path p' -> Sub p -- administrative
>   Redirected :: Path pth -> Underlying a pth s -> Sub p
> deriving instance Show (Sub p)

> r0 = Ctor (S Z) `App` Pntr Z (A1 Here)

> t0 = Ctor (S (S Z)) `App` (Ctor (S Z) `App` Pntr Z (A1 Here))
> t1 = grab Root (A1 Here) t0
> t2 = grab Root (A2 $ A1 Here) t0
> t3 = grab Root (A2 $ A2 Here) t0
> t10 = Ctor (S (S Z)) `App` (Ctor (S Z) `App` Pntr (S Z) (A1 Here))
> t13 = grab Root (A2 $ A2 Here) t10
> t20 = Ctor (S (S Z)) `App` (Ctor (S Z) `App` Pntr (S Z) Here)
> t23 = grab Root (A2 $ A2 Here) t20
> t30 = Ctor (S (S Z)) `App` (Ctor (S Z) `App` Pntr Z Here)
> t33 = grab Root (A2 $ A2 Here) t30
> t34 = grab Root (A2 $ A2 (A1 Here)) t30

Unify (for now) checks whether two trees are unifiable

> unify :: Path here -> Underlying a here s -> Underlying b here u -> Bool
> unify here (Ctor Z) (Ctor Z) = True
> unify here (Ctor (S m)) (Ctor (S n)) = unify here (Ctor m) (Ctor n)
> unify here (l1 `App` r1) (l2 `App` r2) = unify (A1 here) l1 l2 && unify (A2 here) r1 r2
> unify here (Pntr m p) (Pntr n q) = sameNat' m n && samePath p q
> unify _ _ _ = False

> u0 = Ctor (S (S Z)) `App` (Ctor (S Z) `App` Ctor Z)
> u1 = unify Root u0 u0
> u2 = unify Root u0 t0
> u3 = unify Root t0 t0


