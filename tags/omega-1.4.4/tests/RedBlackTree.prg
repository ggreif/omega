
otherwise = True

{-
\subsection{Red-Black Tree Invariants}
A red-black tree is a binary search tree with the following additional invariants:
\begin{enumerate}
\item Each node is colored either red or black
\item The root is black
\item The leaves are black
\item Each Red node has Black children \label{RedKidsAreBlack}
\item for all internal nodes, each path from that node to a descendant 
        leaf contains the same number of black nodes.
\end{enumerate}
We can encode these invariants by thinking of each internal node as 
having two attributes: a color and a black-height.
-}

data RBTree = forall n. Root (SubTree Black n)

kind Color  = Red | Black
 
data SubTree :: Color ~> Nat ~> *0 where
   Leaf :: SubTree Black Z
   RNode :: (SubTree Black n) -> Int -> (SubTree Black n) -> SubTree Red n
   BNode :: (SubTree cL m) -> Int -> (SubTree cR m) -> SubTree Black (S m)
   Fix :: (SubTree Red n) -> SubTree Black n

 
f :: Int -> SubTree c n -> SubTree c n
f n Leaf = (Fix (RNode Leaf n Leaf))
f n (BNode x m y) | n <= m = black (f n x) m y
f n (BNode x m y) | n > m = black x m (f n y)
f n (RNode x m y) | n <= m = RNode (f n x) m y
f n (RNode x m y) | n > m = RNode x m (f n y)
 
black :: SubTree c n -> Int -> SubTree d n -> SubTree Black (S n)
black (RNode (Fix u) v c) w (x@(RNode _ _ _)) = Fix(RNode (blacken u) v (BNode c w x))

black (RNode (Fix u) v c) w (x@(BNode _ _ _)) = BNode u v (RNode c w x)
black (RNode a v (Fix (RNode b u c))) w (x@(BNode _ _ _)) = BNode (RNode a v b) u (RNode c w x)
black (Fix x) n (Fix y) = BNode x n y
black x       n (Fix y) = BNode x n y
black (Fix x) n y       = BNode x n y
black x       n y       = BNode x n y

 
-- Leaf  :: SubTree Black Z
-- RNode :: SubTree Black u -> Int -> SubTree Black u -> SubTree Red u
-- BNode :: SubTree cL n -> Int -> SubTree cR n -> SubTree Black (S n)

blacken :: SubTree Red n -> SubTree Black (S n)
blacken (RNode l e r) = (BNode l e r)
 
