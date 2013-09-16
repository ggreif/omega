
%{


\section{Typed CPS Transform}

\newcommand{\cpsC}[1]{\langle\hspace{-0.2em}\vert {#1} \vert\hspace{-0.2em}\rangle}
\newcommand{\cpsV}[1]{\langle {#1} \rangle}
\newcommand{\cpsE}[1]{\lbrace\hspace{-0.2em}\vert {#1} \vert\hspace{-0.2em}\rbrace}
\newcommand{\lam}[2]{\lambda {#1}.\; {#2}}

We now give an \Wmega{} implementation of the call-by-value CPS 
transform as presented by Hatcliff and Danvy~\cite{hatcliff-danvy-thunks}.
They use the following syntax:
\[
\begin{array}{llcl}
(comp.)& m, n & ::= & v \mid m\ n \\
(value) & v    & ::= & i \mid x \mid \lam{x}{n} \\
\end{array}
\quad
\begin{array}{llcl}
(type) & \tau & ::= & Int \mid \tau \to \tau \mid R \\
(env.) &  \Gamma&::=& \cdot \mid \Gamma, x:\tau \\
\end{array}
\]
Lambda terms are divided into values and computations.  
We commit here to a call-by-value source language by categorizing 
variables as values.  The type $R$ is a special type introduced by the 
CPS transform as the final result type of any computation.

Then they define a call-by-value CPS transform on terms.
\[
\begin{array}{lcl}
\cpsC{v}     &=& \lam{k}{k\ \cpsV{v}} \\
\cpsC{m\ n}  &=& \lam{k}{\cpsC{m}\ (\lam{y_0}{\cpsC{n}\ (\lam{y_1}{y_0\ y_1\ k})})} \\
\end{array}
\quad
\begin{array}{lcl}
\cpsV{i}     &=& i \\
\cpsV{x}     &=& x \\
\cpsV{\lam{x}{n}} &=& \lam{x}{\cpsC{n}} \\
\end{array}
\]
The CPS transform has the following effect on types (and type environments):
\[
\begin{array}{lcl}
\cpsC{\tau}    &=& (\cpsV{\tau} \to R) \to R \\
\cpsV{Int}     &=& Int \\
\cpsV{\tau \to \sigma}   &=& {\cpsV{\tau} \to \cpsC{\sigma}} \\
\end{array}
\quad
\begin{array}{lcl}
\cpsE{\cdot}   &=& \cdot \\
\cpsE{\Gamma,x:\tau} &=& \cpsE{\Gamma},x:\cpsV{\tau} \\
\end{array}
\]

Following two (impressive looking) theorems express that the
CPS translation is type preserving:

If $\Gamma \vdash n : \tau$ then $\cpsE{\Gamma} \vdash \cpsC{n} : \cpsC{\tau}$ and

if $\Gamma \vdash v : \tau$ then $\cpsE{\Gamma} \vdash \cpsV{v} : \cpsV{\tau}$.

\noindent
Our implementation of CPS in \Wmega{} will prove these theorems using
type checking alone.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Type Representations and Singleton Types} \label{single}
%format Res = "R"

The types of the object language can be modelled by \Wmega{} types. 
Since \Wmega{} already has |Int| types and function types (|_ -> _|), 
we only need introduce a new type |Res|.

>data Res = FinalAnswer

We can define a \emph{representation type} for the subset of \Wmega{}'s
type language that we will employ in the CPS example. A representation
(a.k.a. singleton) type |T| is a parameterized type. A (run-time) value
of type |T a| represents (or mirrors the shape of) the the static type
|a|. For example consider |Type t| below.

>data Type t
>       =          Int                    where t = Int
>       | ex a b.  Arr (Type a) (Type b)  where t = a -> b
>       |          Res                    where t = Res

Note how every value of type |Type a| has the same shape as |a|. For
example: |Int :: Type Int|, and |Res :: Type Res|, and if |a :: Type x|
and |b :: Type y|, then |Arr a b :: Type (x -> y)|. For example, the value
\mbox{|Arr Int Res|} has type \mbox{|Type (Int -> Res)|}. The useful
property of |Type| is that there is a one-to-one correspondence between
values of type |Type t| and types |t|. Values of type |Type t| are ordinary
run-time values and can be computed over like any other values. Knowing
the shape (which constructors are used to build it) of a value of type |T
t| determines its type, and knowing the type of such a value determines
its shape.This is why they are some times called singleton types.

\hide{
This allows us to substitute run-time checks for static checks
when necessary. We will make use of this important ability
several places in the sequel, and we will be sure and
point this out when we do.
}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Object Terms}

As we describe the CPS transform we make use of two languages.
The object-language represents the programs we are
transforming (CPS terms) and the meta-language (\Wmega{}) describes
the transformation. Object-programs are data in the meta-language.
The \Wmega{} data-structures representing CPS object-programs
are defined using equality qualified types parameterized by two type indexes:
an environment |e|, and an object-level type |t|.  This means that 
\Wmega{}'s type system guarantees that all well-typed
meta-level terms representing object-level terms, represent only well-typed
object-terms.  The technique relies on de Bruijn indices to represent variables.
\cite{Pasalic}


>data Cmp e t   =           Val   (Val e t)
>               |  ex s.    App   (Cmp e (s -> t)) (Cmp e s)
>
>data Val e t   =           Lit   Int                     where t = Int
>               |           Var   (Var e t) (Type t)
>               |  ex a b.  Lam   (Type a) (Cmp (e,a) b)  where t = a -> b
>
>data Var e t   =  ex f.    Zero                          where e = (f,t)
>               |  ex f s.  Succ  (Var f t)               where e = (f,s)

These datatypes correspond to typing judgments and their values
correspond to proofs of those judgments.  We are using nested pairs
(growing to the right) to model typing environments and a fragment of
the \Wmega{} types (as discussed in Section \ref{single} above) to
model object-types. Some examples are germane here.
Shorthand for some common variable indices will prove useful.
>zero  :: Type a -> Cmp (e,a) a
>zero  t = Val (Var Zero t) 
>
>one   :: Type a -> Cmp ((e,a),b) a
>one   t = Val (Var (Succ Zero) t)
>
>two   :: Type a -> Cmp (((e,a),b),c) a
>two   t = Val (Var (Succ (Succ Zero)) t)

Consider representing the object-level term
$\lam{x:Int \to Int}{\lam{y:Int}{x\ y}}$ 
The meta-level term: |m = App (one (Arr Int Int)) (zero Int)|
has type |Cmp ((e,Int -> Int),Int) Int|. 
Notice how the environment is a nested pair. 
By wrapping |m| in two lambdas |Lam (Arr Int Int) (Val (Lam Int m))|,
we obtain a term with type |Val e ((Int -> Int) -> Int -> Int))|


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Reading Off Types}

The abstract syntax includes enough type information to recover 
at run-time the (representation of the) type of any lambda term.

>expType  :: Cmp e t -> Type t
>expType  (Val v)    = valType v
>expType  (App m n)  = codomain (expType m)
>
>valType  :: Val e t -> Type t
>valType  (Lit i)    = Int
>valType  (Var x t)  = t
>valType  (Lam t n)  = Arr t (expType n)
>
>codomain :: Type (a -> b) -> Type b
>codomain (Arr a b)  = b

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Shifting de Bruijn Indices}

The CPS transform introduces new lambda binders for additional 
continuation parameters.  This necessitates incrementing some 
variable indices to point past any newly introduced binder, 
an operation known as a |shift|. 

%format liftShift = "lift"

>shift :: Cmp e t -> Cmp (e,s) t
>shift e                   = shiftE Succ e
>
>shiftE :: (forall t. Var e t -> Var f t) -> Cmp e t -> Cmp f t
>shiftE    f  (App n m)    = App (shiftE f n) (shiftE f m)
>shiftE    f  (Val v)      = Val (shiftV f v)
>
>shiftV :: (forall t. Var e t -> Var f t) -> Val e t -> Val f t
>shiftV    f  (Lit i)      = Lit i
>shiftV    f  (Var x s)    = Var (f x) s
>shiftV    f  (Lam s n)    = Lam s (shiftE (liftShift f) n)
> 
>liftShift :: (forall t. Var e t -> Var f t) -> Var (e,s) t -> Var (f,s) t
>liftShift s  (Zero)       = Zero
>liftShift s  (Succ x)     = Succ (s x)

Since |shift| is really manipulating typing judgments, we can think of 
its type as a kind of weakening lemma for de Bruijn terms.  In this view, 
the |shift| function itself is a \emph{proof} of the lemma (provided it 
terminates on all inputs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{CPS Transform on Types}

Now we define the effect of the call-by-value CPS transform on 
the types of object terms.  This is conveniently expressed 
with \Wmega{}'s type functions.

>cps   :: * ~> * ~> *
>{cps   r t}          = ({cpsv r t} -> r) -> r
>
>cpsv  :: * ~> * ~> *
>{cpsv  r Int}        = Int
>{cpsv  r (a -> b)}   = {cpsv r a} -> {cps r b}
>
>cpse  :: * ~> * ~> *
>{cpse  r ()}         = ()
>{cpse  r (a,b)}      = ({cpse r a},{cpsv r b})

We then reflect the type functions |cps| and |cpsv| at the 
value level.

>cpsT    :: Type r -> Type t -> Type {cps r t}
>cpsT   r t          = Arr (Arr (cpsTv r t) r) r
>
>cpsTv   :: Type r -> Type t -> Type {cpsv r t}
>cpsTv  r Int        = Int
>cpsTv  r (Arr a b)  = Arr (cpsTv r a) (cpsT r b)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{CPS Transform on Terms}

Finally we define the CPS transform on terms.  The transformation 
is given by three functions, one for each syntactic category.  

<cpsC ::  Type r ->  Cmp  e a ->  Cmp  {cpse r e}  {cps   r a}
<cpsV ::  Type r ->  Val  e a ->  Val  {cpse r e}  {cpsv  r a}
<cpsX ::  Type r ->  Var  e a ->  Var  {cpse r e}  {cpsv  r a}

Each function has a |Type r| parameter because
the CPS transform is parameterized by the final result type |r|.  
We are transforming object types as well as object terms: 
the essence of a type-respecting transformation.

The |Var| and |Val| cases are straightforward.  
In fact |cpsX| is operationally the identity function, 
but it has a more complicated type.  
Another curious fact about |cpsX| is that the |Type r| parameter is 
never used, but is necessary for type-checking.  
Otherwise, in the |Succ| case, we can't unify the |r| 
of the calling |cpsX| with the fresh |r'| 
resulting from the recursive call.

>cpsX ::  Type r ->  Var  e a ->  Var  {cpse r e}  {cpsv  r a}
>cpsX r (Zero)     = Zero
>cpsX r (Succ x)   = Succ (cpsX r x)
>
>cpsV ::  Type r ->  Val  e a ->  Val  {cpse r e}  {cpsv  r a}
>cpsV r (Lit i)    = Lit i
>cpsV r (Var x t)  = Var (cpsX r x) (cpsTv r t)
>cpsV r (Lam t n)  = Lam (cpsTv r t) (cpsC r n)

The |Cmp| cases are the most involved, as they introduce 
new binders for continuation parameters.  This is where 
we need the |shift| operation.

%format y0t = "yt_0"
%format y1t = "yt_1"

>cpsC :: Type r -> Cmp e a -> Cmp {cpse r e} {cps r a}
>cpsC r (Val v)    = Val (Lam kt (App (zero kt) (shift (Val v'))))
>    where  v'     = cpsV r v
>           kt     = Arr (valType v') r
>
>cpsC r (App m n)  = case expType m' of 
>                    Arr (Arr (y0t@(Arr y1t (Arr kt _))) _) _ -> 
>                       Val (Lam kt                                
>                       (App (shift m')          (Val (Lam y0t     
>                       (App (shift (shift n'))  (Val (Lam y1t     
>                       (App (App (one y0t) (zero y1t)) (two kt))  
>                       ))) ))) )
>    where  m'     = cpsC r m
>           n'     = cpsC r n

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\hide{
>-- playing
>exp = Val (Lam Int
>     (Val (Lam (Arr Int Int)
>     (App (zero (Arr Int Int)) (one Int)))))
> 
>test = cpsC Res exp
>-- lam k. k (lam a. lam k. k (lam f. lam c. (lam k. k f) (lam d. (lam k. k a) (lam e. d e c))))
}

%}
