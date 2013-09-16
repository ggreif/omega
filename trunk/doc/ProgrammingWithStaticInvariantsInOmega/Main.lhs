\documentclass[10pt]{article}
%include lhs2TeX.fmt
%include lhs2TeX.sty

\usepackage{latexsym}
\usepackage{fancyvrb}
\usepackage{graphics}
\usepackage{multicol}

\newcommand{\Wmega}{\ensuremath{\Omega}mega}
\def\NN{\mathbb{N}}

% author commands
\newcommand{\hide}[1]{}
\newcommand{\edit}[1]{\marginpar{\raggedright\footnotesize{#1}}}
%\newcommand{\edit}[1]{} % when we're done

\newcommand{\fig}[2]{\parbox[c]{#1}{\includegraphics{#2}}}

%format kind = "{\bf kind}"
%format forall = "\forall"
%format ex = "\exists"
%format ~> = "\leadsto"
%format . = ". "
%format r1 = "r_1"
%format r2 = "r_2"
%format r3 = "r_3"
%format r4 = "r_4"
%format r5 = "r_5"
%format r6 = "r_6"
%format c0 = "c_0"


\title{Programming with Static Invariants in \Wmega{}}
\author{Nathan Linger \& Tim Sheard}

\begin{document}
\maketitle 

\begin{abstract}
We present an implementation of binomial heaps that 
enforces the balancing invariants at compile time.
We present an implementation of a \emph{typed} CPS transform 
that enforces the typing invariants of both the source and target terms.
\end{abstract}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction}

There has been a lot of interest recently in generalizing algebraic
datatypes as found in most functional programming languages. These
generalizations have been called {\it First Class Phantom Types}
~\cite{FirstClassPhantomTypes} {\it Guarded ADTs}~\cite{xi-gadt,
simonet-pottier-hmg} {\it Wobbly types}~\cite{peytonjones-wobbly},
and in our own work {\it Equality Qualified Types}~\cite{GPCE,ONWARD,sheardLFM04}.
Such types allow users to parameterize types with descriptions of 
static properties of their values.
A simple example is the type constructor |Seq| which
describes sequences of elements whose lengths are statically known. For
example |[1,45,2] :: Seq 3 Int|. This says that |[1,45,2]| is a
sequence of |Int| whose length is statically known to be |3|.
A type system employing such a generalization can enforce strong
static invariants.
This leads to programs that are less likely to contain errors, and are
easier to write, since the types often guide the construction of the
function definitions. 

In order to explore these possibilites we implemented
a new language \Wmega. \Wmega\  is descended from Haskell -- 
Its syntax and type system
are similar to Haskell's, but it introduces a new kind of type
constraint (similar to Haskell's class constraints) which constrains
two types to be equal. A function with an equality constrained type, can
only be applied to values whose types force the constrained types to be
the same. This has been described elsewhere~\cite{GPCE,ONWARD,sheardLFM04}, and is
introduced again for the convenience of the reader in 
Section~\ref{IntroOmega}.


This paper introduces several other features of \Wmega{} that work in
combination with equality qualified types (and could also work in combination
with any of the other variants of generalized datatypes) to allow even more
expressive static invariants. These features are user-defined kinds and 
support for functions on types.  The contributions of this paper are:

\begin{itemize} 

\item Demonstrating the usefulness of an extensible kind system. Introducing a new
kind, defines a kind and new types that are classified by that kind.
The new kind is different from the kind that classifies types that
classify values (often called {\it star} or {\it type}). Types introduced
by the kind mechanism make ideal {\em parameters} to equality qualified
data types, and can be used to express a wide variety of static constraints.

\item The ability to define type functions, and the ability to use such
type functions in the types of functions manipulating values with
equality constrained types. Type functions (as opposed to type
constructors such as |List|, and |Tree|) describe computations
on types.  There use is reminiscent of the use of dependent types 
but we claim that \Wmega{}'s type system
implements a simple subset of the dependent types that is simple to
use, understand, and implement. Type functions require a new approach
to unification when integrated into a system with type inference. The
system of equality constrained types provides just the hooks necessary
to do this in a safe and sound manner.\edit{what is meant by "safe and sound"?}


\item We also present two examples in \Wmega{} which
its power to soundly define functions with complex static invariants. 
The two examples are (1) an implementation of binomial heaps and (2) a
typed continuation-passing-style transform.

\end{itemize}

\section{Equality Qualified Types and Kinds in \Wmega{}}\label{IntroOmega}

We introduce equality qualified types by defining the type constructor |Seq|
from above. In order to do this we must also be able to describe natural 
numbers at the type level. To do this we use \Wmega{}'s kind system. The code 
below introduces a new kind |Nat|, new types |Seq|, |Zero|, and |Succ|, 
and a new function |map|.

>kind Nat = Zero | Succ Nat
>
>data Seq a n
>  =         Nil               where n = Zero
>  | ex m .  Cons a (Seq a m)  where n = Succ m
>
>map :: (a -> b) -> Seq a n -> Seq b n   
>map f (Nil)        = Nil
>map f (Cons x xs)  = Cons (f x) (map f xs)

\begin{figure}[t]
%\hspace*{1.4in}
\begin{center}
\begin{tabular}{ccccc}\hline
value & & type & & kind \\ \hline
5     &::& Int  &::& *    \\ %\hline
      &  & Zero &::& Nat \\ %\hline
      &  & Succ &::& Nat $\leadsto$ Nat \\ %\hline      
      &  & Seq &::& * $\leadsto$ Nat $\leadsto$ *  \\ %\hline
Nil   &::& Seq $\,\alpha\;$ Zero &::& * \\ %\hline
Cons  &::& $\alpha \rightarrow$ Seq $\alpha\; n \rightarrow$ Seq $\alpha\; ($Succ$\,n)$ &::& * \\ \hline
\end{tabular}
\end{center}
\caption{Classification of values (Nil,Cons), and types (Zero,Succ, and Seq).}\label{kindtable}
%\hrule
\end{figure}   

The kind declaration for |Nat| introduces two new
type constructors |Zero| and |Succ| which encode the natural
numbers at the type level.
Kinds are similar to types in that, while types classify values, kinds
classify types. We indicate this by the {\em classifies} relation |(::)|. For
example: |5 :: Int :: *|. We say |5| is classified by |Int|,
and |Int| is classified by |*| (star-zero). 
\hide{
The kind |*| classifies all types that classify values (things we actually can
compute). |*| is classified by |*1|, etc. There is an infinite hierarchy of
classifications.  We call this hierarchy the {\em strata}. In fact this
infinite hierarchy is why we chose the name \Wmega. The first few strata are:
values and expressions that are classified by types, types that are
classified by kinds, and kinds that are classified by sorts, etc.}
Figure~\ref{kindtable} illustrates the relationship between the 
values, types, and kinds introduced above.

Constructor functions |Nil| and |Cons|
construct elements of the |Seq| datatype. The type of a constructor function
is described in the datatype declaration. For example, the 
following clause in the
|Seq| declaration:
<ex m . Cons a (Seq a m) where n = Succ m 
introduces the |Cons| constructor function. Without the |where|
qualification, the constructor function |Cons| would have type 
|Cons::a -> Seq a m -> Seq a n|. The |where| {\em  qualifies} |Cons|'s type, in effect
saying |(Cons::a -> Seq a m -> Seq a n)| provided |n=Succ m|. We
capture this formally by writing the equality qualified type |Cons::(forall a n m.(n=Succ m)=> a -> Seq
a m -> Seq a n)|. The equations behind the {\em fat arrow} (|=>|) are
equality qualifications. Since |n| is a universally quantified type
variable, there is only one way to {\em solve} the qualification |n=Succ m|
(by making |n| equal to |Succ m|). Because of this unique solution,
|Cons| also has the (less general) type |(forall a m.a -> Seq a m -> Seq a (S
m))|. This type guarantees that |Cons| can only be applied in contexts
where |n=Succ m|. \hide{Existential quantification of the type variable |m|
names the intermediate length of the sublist of |Cons|, which if not
introduced in this way would appear as an unbound type variable.
{\em Equality Qualification} (indicated by the |where| in the clauses for |Nil|
and |Cons|), and {\em existential quantification} (indicated by |ex|
in the clauses for |Cons|) are the features of \Wmega{} that
are used to encode semantic properties.}


Each data-constructor declaration in \Wmega{} may contain a |where|
clause containing a list of type equations.
The mechanism \Wmega{} uses to keep track of type equalities 
is similar to type class system of Haskell.
A special qualified~\cite{J92}
type is used to assert equality between types, and a
constraint solving system is used to track, propogate, simplify and discharge these
assertions. Equality constraints are tracked in much the same manner as
class constraints in Haskell. For example, 
when assigning a type to a type constructor, the equations
specified in the |where| clause just become predicates in a
qualified type. 
Thus, the constructor |Cons| is given the
type |(forall a m n . (n = Succ m) => a -> Seq a m -> Seq a n)|
The equation |n = Succ m| is just another form of predicate, similar
to the class membership predicate |(Ord a)| in the Haskell type |(==) :: Ord a => a -> a -> Bool|).

{\bf Tracking equality constraints.} When type-checking an expression,
the \Wmega{} type checker keeps two sets of equality constraints:
{\em obligations} and {\em assumptions}.

{\it Obligations.} The first set of constraints is a set of
{\em obligations}.  Obligations are generated by the type-checker
when (a) the program constructs data-values with constructors
that contain equality constraints; or (b) an explicit type signature in a
definition is encountered; or (c) when type functions are used (see Section
\ref{typefun}).

For example, consider type-checking the expression |Nil|. The constructor
|Nil| is assigned the type |forall a n . n=Zero => Seq a n|,
thus |Nil :: Seq a n| but also generates the obligation |n=Zero|. Since |Nil| is
polymorphic in |a| and |n|, the type variable |n| can be instantiated to |Zero|.
Instantiating |n| to |Zero| makes the equality constraint obligation |Zero=Zero|,
which can be trivially discharged by the type checker. Other
constraints may require more work to discharge.

{\it Assumptions.} The second set of constraints is a set of
{\em assumptions} or {\em facts}. Whenever, a constructor 
based pattern appears in a binding position, and the constructor
was defined using a |where| clause, the type equalities in
the |where| clause are added to the current set of assumptions in the
scope of the pattern. These assumptions can be used to discharge
obligations. For example, consider type checking the definition of |map|.
Recall |map:: (a -> b) -> Seq a n -> Seq b n|.

In the first equation, the pattern |Nil| of type |Seq a n| introduces the
assumption |n=Zero| because of |Nil|'s qualified type |forall a n . n=Zero => Seq a
n| This assumption can be used to discharge obligations incurred on the right
hand side of the equation.  Now, consider the second 
equation |map f (Cons x s) = Cons (f x) (map f xs)|. We
know |map|'s type, so the second pattern |(Cons x xs)| must have type |(Seq
a n)|. This implies |x :: a| and |xs :: Seq a m| provided |n = Succ m|. This
equation is added to the list of assumptions when typing the
right-hand-side of the second equation: |Cons (f x) (map f
xs)|. This right-hand-side should have type |(Seq b n)| (the range of |map|'s type). Since |xs
:: Seq a m| we can compute |(map f xs) :: Seq b m|, Since |x :: a| we can
compute |(f x) :: b|, thus it appears |(Cons (f x) (map f xs)) :: Seq b (Succ
m)|. But given the equality constraint |n = Succ m| the right hand side has
type |Seq b n| as expected.
Equality qualified types can encode powerful static invariants about
data. For example the type of |map| provides a proof that |map|
returns a list of the same length as its input list.

\section{Type functions in \Wmega}\label{typefun}

We now introduce type-functions. To see why this is necessary
we ask the rhetorical question: {\em What is the type of the append
function on static-length lists}? The append function should have type
|Seq a n -> Seq a m -> Seq a (n+m)|. In
order to type such functions it is necessary to do arithmetic at
the type level. This means defining functions over types. In \Wmega{}
we do this by writing equations over types. We surround type-function
application by braces (e.g. |{sum x y}|) to distinguish
it from type-constructor application (e.g. |List Int|). We also define
the type-function |sum| and the value-function |append| of static sequences.\\


>sum :: Nat ~> Nat ~> Nat
>{sum Zero      m}  = m
>{sum (Succ n)  m}  = Succ {sum n m}
>
>append :: Seq a n -> Seq a m -> Seq a {sum n m}
>append (Nil)        ys = ys
>append (Cons x xs)  ys = Cons x (append xs ys)

How is a function, like append, whose type includes a type-function 
application, type checked? And, what
role do the type function equations play in the process? Consider the second
equation: |append (Cons x xs) ys = Cons x (append xs ys)|. From the type
signature of |append|, we know |(Cons x xs) :: Seq a n|, and  |ys :: Seq a m|. We
need to check that the right-hand-side |Cons x (append xs ys)| has type 
|Seq a {sum n m}|. Because |Cons| has an equality qualified type, from
the pattern |(Cons x xs)| we know |(x :: a)| and |(xs :: Seq a k)| plus we
get to add the equality |(n = Succ k)| to the set of assumptions. From this we
can compute that |(append xs ys :: Seq a  {sum k m})|. Thus it appears that the
right- hand-side |Cons x (append xs ys)| actually has type |Seq a (Succ {sum
k m})|. To reconcile this apparent difference, the type checking algorithm
unifies the type |Seq a {sum n m}| with the type |Seq a (Succ  {sum k m})|. This
unification succeeds only if the equation |{sum n m} = Succ  {sum k m}| holds. Since
this cannot always be immediately determined, the unification algorithm
delays unification, and generates and propagates this equation as a new obligation.
After checking
the rest of the right-hand-side (which propagates no additional obligations)
we must discharge the obligation |{sum n m} = Succ {sum k m}| under the assumption |(n = Succ k)|.
We use the assumption by substituting |Succ k| for |n|, and then discharge |{sum
(Succ k) m} = Succ {sum k m} |. By applying the second clause in the definition of
|sum| we get |Succ {sum k m} = Succ {sum k m}| which is finally discharged.

By delaying the use of both assumptions and type-function equations until
after all other unification is performed, we avoid the problem that sometimes
occurs when type variables are not instantiated in time. For example
without knowing that |n=Succ k| we could not apply the type-function
rule reducing |sum n m| to |Succ {sum k m}|. 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%include BinomialHeap.lhs

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%include CPS.lhs

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Alternatives to Type-Functions}

There are a few alternatives to the use of type functions of \Wmega{}. We
explore them here because they can be used to give a sound basis to a
semantics for type functions. But while they are sound and do not require
the additional mechanism required by type functions, they are often clumsy
and hard to use. Our addition of type functions to \Wmega was inspired by
programming these more tedious examples, and wondering how we could make our
lives easier. Throughout this section we illustrate the techniques using the
|sum|/|append| example.

>sum :: Nat ~> Nat ~> Nat
>{sum Zero      m}  = m
>{sum (Succ n)  m}  = Succ {sum n m}
> 
>append :: Seq a n -> Seq a m -> Seq a {sum n m}
>append (Nil)        ys = ys
>append (Cons x xs)  ys = Cons x (append xs ys)


One alternative is to use a datatype of explicit ``proofs'' of the 
addition relation.  This datatype is the relational incarnation of the 
|sum| type function.
>data Sum n m s 
>  =             Base                where n = Zero,     s = m
>  | ex n' s' .  Step (Sum n' m s')  where n = Succ n',  s = Succ s'
> 
>append :: Sum n m s -> Seq a n -> Seq a m -> Seq a s   
>append  (Base)      (Nil)        ys = ys
>append  (Step sum)  (Cons x xs)  ys = Cons x (append sum xs ys)


This alternative has the disadvantage of requiring an extra |Sum| 
input.  We can overcome this limitation by giving 
|append| the type 
|Seq a n -> Seq a m -> ex s. (Sum n m s,Seq a s)|.
Since \Wmega{} doesn't directly support existential types in this way, 
we simulate them using a combination of rank-2 polymorphism and 
continuation-passing style.
>append :: Seq a n -> Seq a m -> (forall s. Sum n m s -> Seq a s -> r) -> r
>append (Nil)        ys k = k Base ys
>append (Cons x xs)  ys k = append  xs ys (\sum zs ->
>                                   k (Step sum) (Cons x zs))

In a language supporting multi-parameter type classes with 
functional dependencies~\cite{FunctionalDependencies}
(as do common extensions to Haskell), 
\edit{Does this actually work?  Try it out in GHC!}
we can forego explicitly constructing |Sum| proofs.
We instead define a type class for the |Sum| relation, following
Hallgren~\cite{hallgren-fun}
>class Sum n m s | n m -> s                         where {}
>instance               Sum  Zero      m  m         where {}
>instance Sum n m s =>  Sum  (Succ n)  m  (Succ s)  where {}
Then we use the same CPS trick, but omitting the proof objects.
>append :: Seq a n -> Seq a m -> (forall s. Sum n m s => Seq a s -> r) -> r
>append (Nil)        ys k = k ys
>append (Cons x xs)  ys k = append xs ys (\zs -> k (Cons x zs))
Type inference introduces all the proof objects as implicit 
dictionary arguments.  In this case, the dictionaries are empty 
and should be optimized away.

We can also wrap up the guarded existential in a datatype, but the end 
result is essentially a verbose version of continuation-passing-style.  
Which one is preferable is a matter of taste.
>data SumSeq n m = ex s. Sum n m s => SumSeq (Seq a s)

>append :: Seq a n -> Seq a m -> Seq a {sum n m}
>append (Nil)        ys = SumSeq ys
>append (Cons x xs)  ys = case  append xs ys of
>                               SumSeq zs -> SumSeq (Cons x zs)

It remains to be seen whether most interesting uses of type functions 
fall into the set that can be implemented using type classes. 
If so, we would like to use the syntax of type functions as an 
interface to the underlying machinery of type classes with 
functional dependencies.
Neubauer et al make a similar proposal~\cite{FunctionalNotation}.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Related Work}

\subsection{Non-regular datatypes}
Non-regular datatypes can be used to enforce structural 
invariants on datatypes.

	also encode invariants. \\
	sometimes less natural. \\
	cite Okasaki~\cite{okasaki-adventure}, 
	Hinze~\cite{hinze-}. \\

\subsection{Type Functions}
	Fun with Functional Dependencies~\cite{hallgren-fun} \\
	Functional Notation for Functional
		Dependencies~\cite{FunctionalNotation}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusion}

Equality qualified types (as well as several other generalizations of 
  datatypes) allow one to index datatypes with ``values'' describing 
  the structural invariants they obey.

In a non- dependently-typed setting, these ``values'' must themselves 
be types.
User-defined kinds allow us to define simple datatypes at the type level 
  and enforce that their ``values'' are well-formed.
Type functions provide an intuitive way to compute with type-level data. 

We presented two examples of structural invariants that can be expressed 
  by equality qualified types.  The first example captured the structural 
  invariants of a heap datatype that are relevant for guaranteeing the 
  time-complexities of the heap operations.  The encoding is much more 
  natural than what can be obtained using non-regular datatypes (in the 
  similar setting of red-black trees).

In the second example, the structural invariants were the typing 
  rules of a simple object language.  The first order nature of \Wmega{}'s
  type system forced us to commit to using de Bruijn indices to 
  represent variables. 

In both examples, user-defined kinds and type functions nicely support  
  programming with equality qualified types.  The resulting programs 
  are not to complicated to understand. (We hope!)

We saw how representation types are a useful alternative to dependent types. 
  They provide a flow of information from the value realm to the type realm.

Finally, we argue that while
  type functions allow for elegant code, they need a more solid foundation.
  In particular, we would like to formalize them as an interface to the 
  well-understood mechanism of type classes with functional dependencies.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% BIBLIOGRAPHY
%\bibliographystyle{splncs}
\bibliographystyle{plain} %{alpha}
\bibliography{references}

\section{Appendix: Code for |minElem| and |extractMin|}
%include HeapAppendix.lhs

\end{document}

