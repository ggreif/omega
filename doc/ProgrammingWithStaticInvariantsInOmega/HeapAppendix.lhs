
\subsection{Retrieving the Minimum Element} 

\hide{
Retrieving the minimum element from a binomial heap is fast 
because of the heap invariant maintained for binomial trees.
The only binomial tree operations used in 
the heap code so far are |singletonT| and |mergeT|.
These both maintain the invariant that every binomial tree (and 
subtree) has a minimum element at the top.  So we just need to 
check the top elements of each binomial tree when looking for 
the minimum element of a heap.  This can be done in a single 
$O (log\ n)$ traversal of the list of binomial trees.

The search takes place in two stages.  In the first stage, 
we don't know if the heap is empty so we return 
a |Maybe Elem|.  Once we find a tree (and its top element), we enter 
the second stage, carrying along the least |Elem| found so far.
The entire computation has a top-level wrapper function.
}
%format minElem1 = "minElem_1"
%format minElem2 = "minElem_2"

>minElem :: Heap -> Maybe Elem
>minElem Empty            = Nothing
>minElem (Heap h)         = Just (minElem1 h)
>
>minElem1 :: SubHeap n k -> Elem
>minElem1 (Last t)        = top t
>minElem1 (Skip    h)     = minElem1 h
>minElem1 (Cons t  h)     = minElem2 h (top t)
>
>minElem2 :: SubHeap n k -> Elem -> Elem
>minElem2 (Last t)     x  = min x (top t)
>minElem2 (Skip    h)  x  = minElem2 h x
>minElem2 (Cons t  h)  x  = minElem2 h (min x (top t))

\subsection{Removing the Minimum Element}
\hide{
Removing the minimum element is slightly more difficult because 
one must do something with the remainder of the tree that loses its 
top element.
The basic idea is to make the following three passes 
\edit{"three passes"? change this wording.} over the list of trees.
\begin{enumerate}
\item Identify the tree containing the minimum element.
\item Remove that tree from the original heap.
\item Make a second heap out of the removed tree (minus its minimum element)
      and merge it with the remaining heap.
\end{enumerate}
Using a programming technique called ``The Zipper''~\cite{huet-zipper}, 
we collapse the first two passes into one.  The idea is that 
one pass returns a |Focus| value representing the heap together with 
a focal point singling out one of the binomial trees.  The 
second pass ``heapifies'' the tree in focus and does the merge.
}

>extractMin :: Heap -> Maybe Heap
>extractMin Empty     = Nothing
>extractMin (Heap h)  = Just (unfocus (minFocus1 Top h))

\subsubsection{``The Zipper''.}
\hide{
 The technique is to define an auxilary data 
structure representing paths from the root of some data structure to 
its sub-parts.  In our case, we define a |Path| type that complements 
the |SubHeap| type.
}

>data Path k    =        Top                    where k = Zero
>               | ex j.  Skip'        (Path j)  where k = Succ j
>               | ex j.  Cons' (T j)  (Path j)  where k = Succ j

\hide{
A |Path k| value contains everything we passed by on the way to 
the $k^{\mathrm{th}}$ tree slot in a |Heap|.
Given a |Path| and |SubHeap|, we can ``zip'' them together 
to recover a |Heap|.
}

>zipHeap :: Path k -> SubHeap n k -> Heap
>zipHeap Top          h = Heap h
>zipHeap (Skip' p)    h = zipHeap p (Skip h)
>zipHeap (Cons' t p)  h = zipHeap p (Cons t h)

\hide{}

>close :: Path k -> Heap
>close Top              = Empty
>close (Skip' p)        = close p
>close (Cons' t p)      = zipHeap p (Last t)

\hide{}

>fill :: Path k -> Maybe (SubHeap n (Succ k)) -> Heap
>fill p Nothing         = close p
>fill p (Just h)        = zipHeap p (Skip h)

\subsubsection{The Focus type.}
\hide{
 Now we define a type for singling 
out one tree in a |Heap|.
}

>data Focus = ex n k. Focus (Path k) (T k) (Maybe (SubHeap n (Succ k)))

\hide{
Once we focus in on the tree containing the minimum element.  We convert it 
into a |Heap| and merge it with what remains of the original |Heap|.
}

>unfocus :: Focus -> Heap
>unfocus (Focus p t mh) = merge (heapify t) (fill p mh)

\hide{
We will need to compare trees-in-focus according to their minimum elements.
}

>key :: Focus -> Elem
>key (Focus _ t _) = top t

\subsubsection{Heapifying a tree.}
\hide{
The |unfocus| function above requires us to be able to turn any tree 
of type |T k| (minus its minimum element) into a |Heap|.  A binomial tree 
without its minimum element is just a forest of trees:
|T (k-1)|, |T (k-2)|, \ldots, |T 0|.  
To form a heap, just reverse the list of these trees.
}

>heapify :: T k -> Heap
>heapify (Tree i f) = reverse1 f
>
>reverse1 :: F k -> Heap
>reverse1 (FNil)          = Empty
>reverse1 (FCons t f)     = reverse2 f (Last t)
>
>reverse2 :: F k -> SubHeap n k -> Heap
>reverse2 (FNil)       h  = Heap h
>reverse2 (FCons t f)  h  = reverse2 f (Cons t h)

\hide{
This operation preserves the heap invariant because each sub-tree in 
|f| was built up using |singletonT| and |mergeT|.
}

\subsubsection{Finding the minimum Focus.}

\hide{
Finding the minimum |Focus| in a tree is just like finding the 
minimum element, except we have to pass along an accumulating |Path| 
parameter in order to build up |Focus| values along the way.
}
%format minFocus1 = "minFocus_1"
%format minFocus2 = "minFocus_2"

>minFocus1      :: Path k -> SubHeap n k -> Focus
>minFocus1 p (Last t)         = Focus p t Nothing
>minFocus1 p (Skip   h)       = minFocus1  (Skip' p) h
>minFocus1 p (Cons t h)       = minFocus2  (Cons' t p) h
>                                          (Focus p t (Just h))
>
>minFocus2      :: Path k -> SubHeap n k -> Focus -> Focus
>minFocus2 p (Last t)     x   = minBy key x (Focus p t Nothing)
>minFocus2 p (Skip    h)  x   = minFocus2  (Skip'   p) h x
>minFocus2 p (Cons t  h)  x   = minFocus2  (Cons' t p) h
>                                          (minBy key x
>                                              (Focus p t (Just h)))

