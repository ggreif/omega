> {-# LANGUAGE GADTs, KindSignatures, StandaloneDeriving, TypeFamilies
>            , MultiParamTypeClasses, FlexibleContexts, FlexibleInstances
>            , UndecidableInstances, NoMonomorphismRestriction #-}

> module Unify where

> import TypeMachinery
> import qualified Data.GraphViz as GV
> import Data.GraphViz.Types.Canonical
> import qualified Data.GraphViz.Attributes.Complete as GA
> import Data.GraphViz.Commands
> import Data.GraphViz.Commands.IO
> import qualified Data.Graph.Inductive.Graph as IG
> import Data.Maybe
> import Data.List
> import Data.Function
> import Control.Concurrent(forkIO)

--------------------------------------------------------------------------------
We have an underlying data model, which consists
of
 o- n-ary constructors (here untyped)
 o- application (future: repeated)
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

The node selection by providing an (absolute) path starting
from the graph root results also in a subgraph. This can be
considered to be an instance of a 'directed container', cf.
Ahman, Chapman and Uustalu
(http://www.cl.cam.ac.uk/~da357/papers/fossacs12.pdf).

Anyway, we want a kind for the shape and a kind for the
path from root so we can address any relevant (non-pointer)
node.

kind Overlying -- shape of Underlying

> data Var; data Ctor; data App a b; data Pntr n p; data Qnt h t

kind Turns -- the way to descend

> data Root; data A1 p; data A2 p; data Here

We also would like to exclude non-addressable nodes
kind Whether = Yes | No

> data Yes; data No

kind Addressable :: Whether -> *1 where { Target :: Addressable Yes; Miss :: Addressable No }
--TODO--

> data Target; data Miss


--------------------------------------------------------------------------------
Underlying data type
====================
                          +---- Path to here
            Arity ---+    |
                     |    |    +---- Shape
                     v    v    v

> data Underlying :: * -> * -> * -> * where
>   Var :: Underlying noArity here Var
>   App :: Underlying (S a) (A1 r) s -> Underlying n (A2 r) u -> Underlying a r (App s u)
>   Ctor :: Nat' n -> Underlying n here Ctor
>   Pntr :: Nat' up -> Path p -> Underlying noArity here (Pntr up p)
>   Qnt :: Underlying a' (A1 r) h -> Underlying a (A2 r) t -> Underlying a r (Qnt h t) -- let a = b in c, ∀a.c, ∃a.c
> deriving instance Show (Underlying a p s)

The Path in Pntr has an additional constraint that it must be Here
or start A1.

Only Apps may home Pntrs, so the constraint on Root Apps is that
all Pntrs point into some Var, App or Ctor below (or at) Root.

> data N; data C r0 r1 -- to build rootee lists

> class NoDangling rootee tree
> instance NoDangling rootee Var
> instance NoDangling rootee Ctor
> instance (NoDangling (C (App l r) rootee) l, NoDangling (C (App l r) rootee) r) => NoDangling rootee (App l r)
> instance NoDangling (C (Qnt Ctor r) rootee) r => NoDangling rootee (Qnt Ctor r)
> instance NoDangling (C Var N) (Pntr Z Here)
> instance NoDangling (C Ctor N) (Pntr Z Here)
> instance NoDangling (C (App l r) rootee) (Pntr Z Here)
> instance NoDangling (C (Qnt Ctor r) rootee) (Pntr Z (A1 Here))
> instance NoDangling (C l N) (Pntr Z p) => NoDangling (C (App l r) rootee) (Pntr Z (A1 p))
> instance NoDangling (C r N) (Pntr Z p) => NoDangling (C (App l r) rootee) (Pntr Z (A2 p))
> instance NoDangling rootee (Pntr n p) => NoDangling (C app0 rootee) (Pntr (S n) p)


Please note that constructors do not have names, they have
positions (addresses) in the tree. We refer to the same constructor
by sharing. A constructor in a different position is a distinct
one and they cannot unify. Variables behave accordingly w.r.t.
positionality, but unify with everything.

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
> grab here (A1 p) tree@(Qnt d _) = grab (A1 here) p d
> grab here (A2 p) tree@(Qnt _ r) = grab' tree (A2 here) here p r
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

Relativize an absolute path, considering an absolute cutoff

> relativize :: Path r -> Path a -> Path a' -> Hidden Path
> relativize acc cutoff a | samePath cutoff a = Hide acc
> relativize acc cutoff (A1 a) = relativize (A1 acc) cutoff a
> relativize acc cutoff (A2 a) = relativize (A2 acc) cutoff a

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
We need to define a monad that provides the associations
and tracks the deferrals.

> unify :: Path here -> Underlying a here s -> Underlying b here u -> Bool
> unify here Var Var = True
> unify here Var x = True -- FIXME: create association
> unify here x Var = True -- FIXME: create association
> unify here (Ctor Z) (Ctor Z) = True
> unify here (Ctor (S m)) (Ctor (S n)) = unify here (Ctor m) (Ctor n)
> unify here (l1 `App` r1) (l2 `App` r2) = unify (A1 here) l1 l2 && unify (A2 here) r1 r2
> unify here (Pntr m p) (Pntr n q) = sameNat' m n && samePath p q
> -- FIXME: pointers to (potential) variables must be deferred
> -- FIXME: we can also catch some types of App cycles here
> -- FIXME: due to variables the same constructor may appear at different paths
> --        in the lhs and rhs graphs. So a pre-pass is assumed that ensured
> --        this already. But since Ctor symbols tend to be defined globally,
> --        this probably won't be a problem.
> unify _ _ _ = False

> u0 = Ctor (S (S Z)) `App` (Ctor (S Z) `App` Ctor Z)
> u1 = unify Root u0 u0
> u2 = unify Root u0 t0
> u3 = unify Root t0 t0

--------------------------------------------------------------------------------
Parsing support
===============
TBI

Parsec Haskellstyle

--------------------------------------------------------------------------------
Pretty-printing
===============
TBI

given original dictionary (abspath <-> Ctor name)

--------------------------------------------------------------------------------
Visualization by GraphViz
=========================

> data TermGraph n e where
>   NoTerm :: TermGraph n e
>   Term :: NoDangling N s => Path p -> [IG.Node] -> Underlying a p s -> Int -> TermGraph n e
> deriving instance Show (TermGraph n e)

Given a natural number we can generate a relative path
by unfolding the binary representation:
 o 1 ->       Here
 o 2 ->    A1 Here
 o 3 ->    A2 Here
 o 4 -> A1 A1 Here
 o 5 -> A1 A2 Here
 o 6 -> A2 A1 Here
 o ...

> nodeToPath' :: Path r -> Int -> Hidden Path
> nodeToPath' acc 1 = Hide acc
> nodeToPath' acc n | 0 <- n `mod` 2 = nodeToPath' (A1 acc) (n `div` 2)
> nodeToPath' acc n | 1 <- n `mod` 2 = nodeToPath' (A2 acc) (n `div` 2)
> nodeToPath :: Int -> Hidden Path
> nodeToPath n = nodeToPath' Here n

> pathToNode' :: Int -> Hidden Path -> Int
> pathToNode' acc (Hide Here) = acc
> pathToNode' acc (Hide (A1 p)) = pathToNode' (acc * 2) (Hide p)
> pathToNode' acc (Hide (A2 p)) = pathToNode' (acc * 2 + 1) (Hide p)
> pathToNode :: Hidden Path -> Int
> pathToNode p = pathToNode' 1 p


> rootTerm = Term Root
> fullRootTerm t = Term Root [] t $ noTermNodes t

Counting nodes (not the addressable subtrees)

> noTermNodes :: Underlying a p s -> Int
> noTermNodes (d `Qnt` r) = 1 + noTermNodes d + noTermNodes r
> noTermNodes (l `App` r) = 1 + noTermNodes l + noTermNodes r
> noTermNodes _ = 1

Obtaining the list of nodes

> termNodes :: IG.Node -> Underlying a p s -> [IG.Node]
> termNodes baseNode (d `Qnt` r) = baseNode : (termNodes (baseNode * 2) d ++ termNodes (baseNode * 2 + 1) r)
> termNodes baseNode (l `App` r) = baseNode : (termNodes (baseNode * 2) l ++ termNodes (baseNode * 2 + 1) r)
> termNodes baseNode _ = [baseNode]

Base node for an absolute path

> nodeForPath :: Path a -> IG.Node
> nodeForPath Root = 1
> nodeForPath (A1 p) = 2 * nodeForPath p
> nodeForPath (A2 p) = 2 * nodeForPath p + 1

> instance IG.Graph TermGraph where
>   empty = NoTerm
>   isEmpty NoTerm = True
>   isEmpty (Term _ done _ max) = length done >= max
>   match node gr@(Term p done t _) | node `elem` done = (Nothing, gr)
>   match 1 gr@(Term Root _ (Ctor n) _) = (Just ([], 1, undefined, []), NoTerm)
>   match node gr@(Term p done t max) | Hide r <- nodeToPath node
>                            = case grab p r t of
>                              Miss -> (Nothing, gr)
>                              Sub (_ `Qnt` _) -> ( Just ([], node, undefined, [(undefined, node * 2), (undefined, node * 2 + 1)])
>                                                 , Term p (node:done) t max)
>                              Sub (_ `App` _) -> ( Just ([], node, undefined, [(undefined, node * 2), (undefined, node * 2 + 1)])
>                                                 , Term p (node:done) t max)
>                              Sub _ -> (Just ([], node, undefined, []), Term p (node:done) t max)
>                              Redirected p' t' -> ( Just ([], node, undefined, [(undefined, pathToNode $ relativize Here p p')])
>                                                  , Term p (node:done) t max)
>   mkGraph _ _ = error "Cannot build graphs through the 'mkGraph' interface"
>   labNodes NoTerm = []
>   labNodes term@(Term p _ t max) = [IG.labNode' ctx | n <- termNodes (nodeForPath p) t
>                                                     , let (present,_) = IG.match n term
>                                                     , isJust present
>                                                     , let Just ctx = present]

> g0 = (Ctor (S Z)) `App` Pntr Z (A1 Here)
> g1 :: TermGraph () ()
> g1 = fullRootTerm g0
> g2 :: TermGraph () ()
> g2 = fullRootTerm r0
> g3 = termVisualizer g2
> g4 = preview' g3
> g5 = fullRootTerm $ Ctor (S Z)
> g6 = termVisualizer g5
> g10 = (Ctor (S $ S Z) `App` Ctor Z) `App` (Pntr (S Z) (A1 $ A1 Here) `App` Pntr (S Z) (A1 $ A2 Here))
> g11 :: TermGraph () ()
> g11 = fullRootTerm g10
> g12 = termVisualizer g11
> g13 = preview' g12
> g20 = Ctor (S Z) `App` Var
> g21 = fullRootTerm g20
> g22 = termVisualizer g21
> g23 = preview' g22
> g30 = Ctor (S Z) `Qnt` ((Pntr (S Z) (A1 Here)) `App` Ctor Z)
> g31 = fullRootTerm g30
> g32 = termVisualizer g31
> g33 = preview' g32


-- TODO: supply attributes to GV, Ctor with name, App, MultiApp n

Finding a hierarchical structure for terms

> ranks :: [IG.Node] -> [(GV.GraphID, [IG.Node])]
> ranks ns = clusters
>       where groups = groupBy ((Prelude.==) `on` fst) $ map (\n->(getStratum 0 n, n)) (sort ns)
>             clusters = map (\g@((r,_):_) -> (Int r, map snd g)) groups
>             getStratum acc 0 = acc
>             getStratum acc n = getStratum (acc + 1) (n `div` 2)


Visualization of TermGraphs as DotGraphs

> termVisualizer :: TermGraph nl el -> DotGraph IG.Node
> termVisualizer tg = rankNodes $ GV.graphToDot params { GV.isDirected = True
>                                                      , GV.fmtNode = nodeShaper
>                                                      , GV.fmtEdge = edgeShaper } tg
>      where params = GV.nonClusteredParams
>            nodeRanks (Term p done t _) = ranks $ termNodes (nodeForPath p) t \\ done
>            nodeRanks _ = []
>            rankNodes g = g { strictGraph = True, graphStatements = rankNodes' $ graphStatements g }
>            rankNodes' stmts = stmts { subGraphs = map (uncurry mkSubgraph) (nodeRanks tg) }
>            mkSubgraph _ ns = DotSG { isCluster = False, subGraphID = Nothing
>                                     , subGraphStmts = DotStmts { attrStmts = [GraphAttrs {attrs = [GA.Rank GA.SameRank]}]
>                                                                , subGraphs = []
>                                                                , nodeStmts = map simpleNode ns, edgeStmts = [] } }
>            simpleNode n = DotNode { nodeID = n, nodeAttributes = [] }
>            edgeShaper ed@(f, t, _) = GV.fmtEdge params ed ++ extraEdgeShape f tg
>            extraEdgeShape f (Term p _ t _)
>                           | Hide r <- nodeToPath f
>                           , Redirected _ _ <- grab p r t
>                           = [ GV.edgeEnds GV.Both, GA.TailClip False, pointerTail
>                             , GA.ArrowSize 0.7, GA.Color [GA.X11Color GA.Blue]
>                             , GA.Weight 0.0 ]
>            extraEdgeShape _ _ = []
>            pointerTail = GV.arrowFrom GV.dotArrow
>            nodeShaper nd@(n, _) = GV.fmtNode params nd ++ extraNodeShape n tg
>            extraNodeShape n (Term p _ t _)
>                           | Hide r <- nodeToPath n
>                           , Redirected _ _ <- grab p r t
>                           = [GA.Width 0.2, GA.Height 0.2, GV.toLabel "", GA.Shape GA.BoxShape]
>            extraNodeShape n (Term p _ t _)
>                           | Hide r <- nodeToPath n
>                           = case grab p r t of
>                             Sub Var -> [GV.toLabel "", GA.Shape GA.DiamondShape]
>                             Sub (Ctor n) -> [GV.toLabel $ arity n, GA.Shape GA.Triangle]
>                             Sub (_ `Qnt` _) -> [GV.toLabel "", GA.Shape GA.House]
>                             _ -> []
>            arity :: Nat' n -> String
>            arity Z = ""
>            arity n = '/' : show (fromIntegral $ Hide n)


> preview'   :: DotGraph IG.Node -> IO ()
> preview' dg = ign $ forkIO (runGraphvizCanvas' dg Xlib)
>   where
>     ign = (>> return ())

--------------------------------------------------------------------------------
Laundry list:
=============

 - we need a way to "break out" a part of the global graph to a smaller
   local (but rooted) one so we can benefit from our fast unification
   algorithm. When we are done we can "merge back" the results. Otherwise
   we have a high Pntr/Ctor ratio, which causes many deferrals of Pntr
   lookups.

 - narrowing. Primarily needed for dealing with type functions:
    o unify from left with args and from right with result
    o find the remaining equations, and
    o connect left with right for each of them by lazily diagonalizing
      over the type variables inside. The generators would be n (> 0) paths
      into a tree addressing n variables. Each path needs to be accompanied
      with a set of applicable constructors based on the variable's type.

 - Can we come up with a clever scheme to identify (views?)
   thrist of trees and tree of thrists? Rebuilding is probably too
   expensive. Are these commutative functors (-> Andy Gill) ?
   Could we convince the compiler to add the extra pointers to these
   structures so we can travel in either direction? Tree-wise or thrist-
   wise at will?