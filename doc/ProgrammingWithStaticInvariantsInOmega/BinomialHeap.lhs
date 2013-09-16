
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Binomial Heaps}

%{

Binomial Heaps are a collection
type that support the following operations, 
each listed with its time complexity.

<empty       :: Heap                  --  $O(1)$
<singleton   :: Elem -> Heap          --  $O(1)$
<insert      :: Elem -> Heap -> Heap  --  $O(lg\ n)$
<merge       :: Heap -> Heap -> Heap  --  $O(lg\ n)$
<minElem     :: Heap -> Maybe Elem    --  $O(lg\ n)$
<extractMin  :: Heap -> Maybe Heap    --  $O(lg\ n)$

That every operation takes logortihmic (or better) time
is due to a sophisticated set of invariants that structure
the binomial heap. Correctly implementing heap operations 
that maintain these invariants is a non-trivial task.
Any help in this endeavor is greatly appreciated. 
In \Wmega{} we can express almost all the invariants 
and let the type checker enforce them.

The |Heap| type should really be parameterized by the type of its 
elements.  For simplicity of exposition, we just treat |Elem| as 
an abstract type that supports comparison operations.  The 
desired parameterization poses no problems but clutters
the presentation of the static properties.

\hide{
>otherwise = True
>
>foldr c n [] = n
>foldr c n (x:xs) = c x (foldr c n xs)
>
>min a b | b < a       = b
>        | otherwise   = a
>
>minBy :: (a -> Elem) -> (a -> a -> a)
>minBy key a b
>       | key b < key a   = b
>       | otherwise       = a
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Natural Numbers as Types}

The datatypes we use to encode binomial heaps are indexed by natural
numbers. These parameters encode structural invariants for each
type. Since we do not use dependent types, we must
develop \emph{types} whose structure mirrors that of the naturals.  For
our purposes here, two representations of numbers are useful. The
natural numbers (|N1|) in unary, and the positive natural numbers (|N2|)
in binary.

%format N1 = "\NN_1"
%format N2 = "\NN_2"

>kind N1 = Zero | Succ N1          -- $0$ or $n+1$
>kind N2 = One | Even N2 | Odd N2  -- $1$ or $2n$ or $2n+1$

The binary representation is least-significant-bit first.
For example, the type |Odd (Even (Odd One))| stands for the 
number $1101_{2} = 13_{10}$.

We encode only positive naturals in the binary representation.
Instead we could include zero by defining
|kind N2 = Zero2 || Even N2 || Odd N2|.
The problem with this definition is that it does not rule out 
trailing zeroes.  For example |Even Zero2| and |Zero2| both 
stand for the number |0|.

We define increment and addition type-functions on the binary representation 
of the naturals.

>inc :: N2 ~> N2
>{inc One}       = Even One
>{inc (Even n)}  = Odd n
>{inc (Odd n)}   = Even {inc n}

Addition is defined as a pair of mutually recursive functions: 
|add| (without carry) and |addc| (with carry).

>add  :: N2 ~> N2 ~> N2
>{add One        m}          = {inc m}
>{add n          One}        = {inc n}
>{add (Even  n)  (Even  m)}  = Even  {add   n m}
>{add (Even  n)  (Odd   m)}  = Odd   {add   n m}
>{add (Odd   n)  (Even  m)}  = Odd   {add   n m}
>{add (Odd   n)  (Odd   m)}  = Even  {addc  n m}
>
>addc :: N2 ~> N2 ~> N2
>{addc One        m}          = {inc {inc m}}
>{addc n          One}        = {inc {inc n}}
>{addc (Even  n)  (Even  m)}  = Odd   {add   n m}
>{addc (Even  n)  (Odd   m)}  = Even  {addc  n m}
>{addc (Odd   n)  (Even  m)}  = Even  {addc  n m}
>{addc (Odd   n)  (Odd   m)}  = Odd   {addc  n m}

\hide{
For clarity, in the remainder of the paper we will use the usual 
mathematical notation for the naturals.  However, the reader should 
remember that all types of kind |N1| or |N2| are built up from the 
constructors presented here.

%%format Zero = "0"
%%format One = "1"
%%format Succ k = "{" k "+1}"
%%format Even n = "2 \cdot " n
%%format Odd n = "2 \cdot " n "+ 1"
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Binomial Trees}

%format (F (k)) = "F_{" k "}"
%format (T (k)) = "T_{" k "}"

Binomial heaps are composed of simpler structures 
called binomial trees, which we explain first. 
The datatype |T k| of binomial trees is based on the arithmetic identity
\[2^k \quad = \quad 1 + (2^{k-1} + 2^{k-2} + \cdots + 2^0)
  \quad \textrm{where } k \geq 0 \]
We also make use of an auxillary 
datatype |F k| of forests (of tress) stored in descending order: $T_{k-1}, T_{k-2},\ldots, T_0$.

>data T k       =        Tree Elem (F k)
>data F k       =        FNil               where k = Zero
>               | ex j.  FCons (T j) (F j)  where k = Succ j

This definition defines type constructors |T( )| and |F( )| of kind |N1 ~> *|.
The |where| clauses in this definition effectively give the data 
constructors the following types:
>Tree   :: Elem -> F k -> T k
>FNil   :: F Zero
>FCons  :: T k -> F k -> F (Succ k)


Trees of type |T k| contain exactly $2^k$ elements.
Forests of type |F k| contain exactly $2^k-1$ elements.
Convince yourself of this by an inductive argument 
based on the types of the data constructors.
Note that the boundary condition $2^0=1$ holds.

>singletonT :: Elem -> T Zero
>singletonT a = Tree a FNil

Before we move to the inductive step we need to discuss
the heap invariant.
Binomial heaps satisfy two kinds of invariants.  The first kind of
invariant is static and structural, having to do with the
relative shapes and sizes of the trees in the heap, and is captured in
the type indexs of the data structures. This is what
the inductive proof is about. The second is the \emph{heap
invariant}. Binomial heaps are composed of Binomial trees. The heap
invariant states the every node in a binomial tree in a binomial heap has
a value no greater than that of any its descendents. The heap invariant
is captured by making the construction of binomial trees abstract.
Singleton trees vacuously meet the heap invariant (they have only one
element) and are made by using the abstract constructor (|singletonT|).
Larger trees are constructed by an abstract constant-time merge function
(|mergeT|)
corresponding to the identity $2^k + 2^k = 2^{k+1}$. We construct
this function in two steps. First we define |mergeT'|:

%format t1 = "t_1"
%format t2 = "t_2"

>mergeT' :: T k -> T k -> T (Succ k)
>mergeT' (Tree e f) t = Tree e (FCons t f)

The top element of |mergeT' t1 t2| is the top element of |t1|. 
A simple wrapper function ensures that merging preserves the heap property
by swapping |t1| with |t2| when necessary.

>top :: T k -> Elem
>top (Tree i _) = i
>
>mergeT :: T k -> T k -> T (Succ k)
>mergeT t1 t2  | top t1 <= top t2  = mergeT' t1 t2
>              | otherwise         = mergeT' t2 t1
                                                                                
So long as we only use |singletonT| and |mergeT| to build trees, we will
preserve the heap invariant. The function |mergeT| also preserves the
structural invariant, which is manifest in its type. This completes the
inductive step of the structural proof. You can't
construct well typed binomial trees, that don't
meet the structural invariant. There is one other function that
needs to break the binomial tree abstraction (used to implement
|extractMin|) but it also preserves the heap invariant.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Binomial Heaps}

As we develop the arithmetic analogy, the binary representation of 
natural numbers is the basis for \emph{binomial heaps}.  Since there 
is a unique binary representation for any natural number $n$, there 
is a unique set of (distinct) binomial tree sizes that together contain 
$n$ elements.  For example, we can contain 13 elements in a collection 
of binomial heaps of types |T 0|, |T 2|, and |T 3| because 
$13 = 2^0 + 2^2 + 2^3$.  In this way, the structure of binomial heaps 
mirrors that of binary numbers.  

Here is a first attempt at defining the |Heap| datatype.

<data Heap n
<   =        Last  (T (?))            where n = One
<   | ex m.  Skip           (Heap n)  where n = Even m
<   | ex m.  Cons  (T (?))  (Heap n)  where n = Odd m

What's missing is an accumulating parameter to specify the orders 
of binomial trees.  We arrive at the following definition.

>data SubHeap n k
>       =        Last (T k)                        where n = One
>       | ex m.  Skip        (SubHeap m (Succ k))  where n = Even m
>       | ex m.  Cons (T k)  (SubHeap m (Succ k))  where n = Odd m
> 
>data Heap = ex n. Heap (SubHeap n Zero) | Empty

A wrapper datatype |Heap| initializes the accumulating parameter at |Zero|.  
The wrapper type also hides the size parameter by binding it 
existentially.  This shields users of the heap library from the 
details of its implementation.

The type constructor |SubHeap| has kind |N2 ~> N1 ~> *|.  We use the 
unary representation to count off the orders of the binomial trees in a heap, 
and the binary representation to determine the shape of the subheap.
Any |SubHeap n k| value contains $n * 2^k$ elements.  
By corollary, a |Heap| value with hidden existential parameter $n$ 
contains $n$ elements.  Figure~\ref{fig:heap} shows an example heap.

\begin{figure*}
\begin{tabular}{lc}
\parbox{2.5in}{
{\small
<SubHeap  (
<   Cons  (Tree 1 FNil) (
<   Skip  (
<   Last  (Tree 2 
<         (FCons  (Tree 4
<                 (FCons (Tree 5 FNil)
<                 FNil))
<         (FCons  (Tree 3 FNil) FNil)) ) 
<    )))
}}
&
\fig{1in}{fig.1}
\\
\end{tabular}
\caption{A binomial heap of size $5_{10} = 101_{2}$.
It contains several sub-heaps. The |Cons| heap has type |SubHeap (Odd (Even One)) Zero|,
the |Skip| heap has type |SubHeap (Even One) (Succ Zero)|, and the
|Last| heap has type |SubHeap One (Succ (Succ Zero))|. Translating
the binary and unary representations in the types to decimal, we
see |Cons| with type |Subheap 5 0|, |Skip| with type |Subheap 2 1|,
and |Last| with type |Subheap 1 2|.  Check for yourself that a heap
with type |Subheap n k| has $n*2^k$ elements.
}

\label{fig:heap}
\end{figure*}

\subsubsection{Primitive Heaps}
Here are primitive heaps containing 0 and 1 elements.

>empty :: Heap
>empty = Empty
>
>singleton :: Elem -> Heap
>singleton a = Heap (Last (singletonT a))

\subsubsection{Insertion}

Inserting a binomial tree into a binomial (sub-) heap corresponds to 
incrementing a binary number.  The tree to be inserted corresponds to 
the least significant ``carry'' bit that is being added on.  This is why 
the |k| parameters of the sub-heap and the tree have to match.
We encourage the reader to compare this definition with the definition 
of |inc|.
%format insertH = "ins"
%format insertH2 = "ins2"

>insertH   :: T k -> SubHeap n k -> SubHeap {inc n} k
>insertH t (Last x)     = Skip (Last (mergeT x t))
>insertH t (Skip    h)  = Cons t h
>insertH t (Cons x  h)  = Skip (insertH (mergeT x t) h)

At top level, we call a wrapper function that inserts a single 
element into a |Heap| as a tree of size $2^0$.

>insert :: Elem -> Heap -> Heap
>insert e Empty     = singleton e
>insert e (Heap h)  = Heap (insertH (singletonT e) h)

We will also need an insertion function corresponding to an 
increment-by-two operation.

>insertH2  :: T (Succ k) -> SubHeap n k -> SubHeap {inc {inc n}} k
>insertH2 t (Last x)     = Cons x (Last t)
>insertH2 t (Skip    h)  = Skip (insertH t h)
>insertH2 t (Cons x  h)  = Cons x (insertH t h)

\subsubsection{Merging}
Adding two binary numbers corresponds to merging two binomial heaps.
Since addition over binary numbers, is defined by mutually 
recursive type functions, we define two mutually recursive 
merge functions, one with an extra binomial tree argument 
(corresponding to a carry bit) and one without.
We encourage the reader to compare these definitions with the definitions 
of |add| and |addc|.
%% shorten the name of the merge functions so they will print properly

>mrg :: SubHeap n k -> SubHeap m k -> SubHeap {add n m} k
>mrg    (Last  x)     m             = insertH x m
>mrg    n             (Last  y)     = insertH y n
>mrg    (Skip     n)  (Skip     m)  = Skip    (mrg                n m)
>mrg    (Skip     n)  (Cons  y  m)  = Cons y  (mrg                n m)
>mrg    (Cons  x  n)  (Skip     m)  = Cons x  (mrg                n m)
>mrg    (Cons  x  n)  (Cons  y  m)  = Skip    (mrgc (mergeT x y)  n m)
>
>mrgc :: T k -> SubHeap n k -> SubHeap m k -> SubHeap {addc n m} k
>mrgc x (Last  y)     m             = insertH2 (mergeT x y) m
>mrgc x n             (Last  z)     = insertH2 (mergeT x z) n
>mrgc x (Skip     n)  (Skip     m)  = Cons x  (mrg                n m)
>mrgc x (Skip     n)  (Cons  z  m)  = Skip    (mrgc (mergeT x z)  n m)
>mrgc x (Cons  y  n)  (Skip     m)  = Skip    (mrgc (mergeT x y)  n m)
>mrgc x (Cons  y  n)  (Cons  z  m)  = Cons x  (mrgc (mergeT y z)  n m)

Again, we define a wrapper function for merging top-level |Heap|s.

>merge :: Heap -> Heap -> Heap
>merge Empty      h2         = h2
>merge h1         Empty      = h1
>merge (Heap h1)  (Heap h2)  = Heap (mrg h1 h2)

\subsubsection{Retrieving and Removing the Minimum Element} 
Due to space considerations, we omit a full exposition of 
the |minElem| and |extractMin| operations.  
The most interesting part of those definitions involves a 
type-indexed ``zipper'' type~\cite{huet-zipper} that represents
|SubHeap| contexts.  This gives evidence that Huet's zipper 
technique scales well to indexed types.
The interested reader may refer to the Appendix for details.

\hide{
> -- FOR TESTING PURPOSES
>
>inserts xs = foldr insert empty xs
>fromJust (Just x) = x
>hd h = fromJust (minElem h)
>tl h = fromJust (extractMin h)
>
>heap0 = inserts[9,6,1,5,0,10,2,8,11,7,4,3,12]
>test = tl(tl(tl(tl(tl(tl(tl(tl(tl(tl(tl(tl(tl(heap0)))))))))))))
}

%}
