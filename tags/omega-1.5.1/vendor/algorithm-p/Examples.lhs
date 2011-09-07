-- Time-stamp: <2010-05-28 17:07:12 cklin>

-- This file contains a small amount of Haskell code in Literate Haskell
-- format (which the parser for my type inference implementation
-- ignores); you can load it directly in GHC if you name this file with
-- the .lhs extension.

> {-# LANGUAGE GADTs, EmptyDataDecls #-}

data Bool where
  { True  :: Bool
  ; False :: Bool }

data Maybe where
  { Nothing :: Maybe a
  ; Just    :: a -> Maybe a }

data La where
  { N :: La a
  ; C :: a -> La a -> La a }

> data L a b where
>   Nil :: L Z a
>   Cons :: a -> L n a -> L (S n) a
> 
> nul :: L a b -> Bool
> nul Nil = True
> nul (Cons _ _) = False

-- My type inference algorithm neither requires nor supports the
-- declaration of type constructors; only data constructors need to be
-- declared along with their types.  Here I simply refer to type
-- constructors Z and S without declaration as if they already exist.

data L where
  { Nil :: L Z a
  ; Cons :: a -> L n a -> L (S n) a }

data App where
  { App :: (a -> b) -> a -> App b }

--------- Data constructors

const1 = 3

const2 = True

const3 = False

const4 = Nothing

const5 = Just

const6 = Just True

const7 = Just Nothing

const8 = N

const9 = C N N

const10 = C (Just 3) (C Nothing N)

-- Naming convention for top-level definitions: a suffix 'x' indicates
-- that the definien is not well-typed in the GADT type system, and a
-- suffix 'o' indicates that the definien is well-typed, but my type
-- inference algorithm fails to a type for the definition.

const11x = C 3 (C True N)

const12x = C 3 True

const13 = Nil

const14 = Cons 3

const15 = Cons N Nil

const16 = Cons Nil Nil

const17 = Cons (Just 3) (Cons Nothing Nil)

const18x = Cons 3 (C 4 N)

const19x = Cons 3 (Cons True Nil)

const20 = App

const21 = App Just 5

const22x = App 5

--------- Simple functions

func1 x = 3

func2 x = 3+x

func3 x y = x+y

func4 x = Just x

func5 x = C x N

func6 x = C 3 x

func7x a = C a a

func8 x y = Cons x y

func9 x = Cons x Nil

func10 f = App f True

func11 f x = f x

func12x f = f f

--------- Let expressions

let1 =
    let { f x = Cons x Nil }
    in (f 3, f True)

let2 =
    let { f x = x }
    in f (f 3)

let3 x =
    let { f y = C x (C y N) }
    in f 3

let4x x =
    let { f y = C x (C y N) }
    in (f 3, f True)

let5 =
    let { f x = C x (f x) }
    in (f 3, f False)

let6 =
    let { f x = f True + 3 }
    in f False

let7 =
    let { f x = 3
        ; g x = (f x, f True) }
    in g False

let8 =
    let { f x = 3
        ; g x = (f (x+3), f True) }
    in g 6

let9 =
    let { f x = C 3 (g x)
        ; g x = C x (f x) }
    in g 7

foldl f a e =
    case e of
      { N -> a
      ; C x xs -> foldl f (f a x) xs }

foldr f a e =
    case e of
      { N -> a
      ; C x xs -> f x (foldr f a xs) }

--------- Case expressions: ADT

adt1 e =
    case e of
      { True -> False
      ; False -> True }

adt2x e =
    case e of
      { True -> False
      ; Nothing -> True }

adt3 e =
    case e of
      { Just a -> a }

adt4 e =
    case e of
      { Just a -> a+2 }

adt5 c e =
    case e of
      { Just a -> a
      ; Nothing -> c }

adt6 e =
    case e of
      { Just a -> a
      ; Nothing -> 3 }

adt7 e =
    case e of
      { C x xs -> xs }

adt8 e =
    case e of
      { App f x -> f x }

adt9x e =
    case e of
      { App f x -> f 3 }

adt10x e =
    case e of
      { App f x -> f }

adt11x e =
    case e of
      { App f x -> x }

adt12 e =
    case e of
      { (a, b) -> a }

adt13 e =
    case e of
      { (a, b) -> b }

adt14x =
    case True of
      { (a, b) -> b }

--------- Case expressions: Non-Dependent GADT

ndep1 e =
    case e of
      { Nil -> True
      ; Cons x xs -> False }

ndep2 e =
    case e of
      { Cons x xs -> x }

ndep3 e =
    case e of
      { Nil -> True
      ; Cons x xs -> x }

ndep4 e =
    case e of
      { Cons x xs -> xs }

ndep5 e =
    case e of
      { Cons x xs -> Cons x xs }

ndep6 e =
    case e of
      { Cons x xs -> Cons False xs }

ndep7x e =
    case e of
      { Nil -> undefined
      ; Cons x xs -> xs }

ndep8 e =
    case e of
      { Nil -> undefined
      ; Cons x xs -> x }

ndep9x =
    case Nil of
      { Cons x xs -> True }

--------- Case expressions: GADT

gadt1 e =
    case e of
      { Nil -> Nil
      ; Cons x xs -> Cons x xs }

gadt2 e =
    case e of
      { Nil -> Nil
      ; Cons x xs -> Cons True xs }

gadt3 e =
    case e of
      { Nil -> Cons True Nil
      ; Cons x xs -> Cons False (Cons x xs) }

gadt4 e =
    case e of
      { Nil -> Just Nil
      ; Cons x xs -> Just (Cons x xs) }

gadt5 e =
    case e of
      { Nil -> Nil
      ; Cons x xs -> e }

gadt6 e =
    case e of
      { Nil -> e
      ; Cons x xs -> Cons False xs }

gadt7o e =
    (case e of { Nil -> True },
     case e of { Cons x xs -> False })

--------- Case expressions: generalized existentials

data K where
  { KInt  :: Int -> K Int
  ; KPair :: a -> b -> K (a, b) }

gext1 e =
    case e of
      { KInt i -> i
      ; KPair a b -> (a, b) }

gext2 e =
    case e of
      { KPair a b -> (a, 3) }

gext3x e =
    case e of
      { KInt i -> i
      ; KPair a b -> (a, 3) }

gext4 e =
    case e of
      { KPair a b -> (a, b+3) }

gext5x e =
    case e of
      { KInt i -> i
      ; KPair a b -> (a, b+3) }

gext6 e =
    case e of
      { KPair a b -> a }

gext7x e =
    case e of
      { KInt i -> Nothing
      ; KPair a b -> Just a }

gext8x e =
    case e of
      { KInt i -> Nothing
      ; KPair a b -> Just (a+3) }

--------- Case expressions: non-pointwise programs

-- The algorithm is capable of inferring the types of some non-pointwise
-- GADT programs due to the separate handling of type parameters and
-- type indices.  In the range type of S1, the type inference algorithm
-- considers the first "a" a type index (which is fixed), and the second
-- "a" a type parameter (which can be further instantiated).  This
-- asymmetry allows type inference for skew1 to succeed with a
-- non-pointwise inferred type, but it also causes type inference for
-- skew2o to fail (because in skew2o it is the first "a" that needs to
-- be a type parameter instead of the second).

data Skew where
  { S1 :: a -> Skew a a
  ; S2 :: Skew Int a
  ; S3 :: Skew Bool a
  ; S4 :: Skew a Int
  ; S5 :: Skew a Bool
  ; S6 :: Skew a b }

skew1 e =
    case e of
      { S1 a -> a
      ; S2 -> True
      ; S3 -> False }

skew2o e =
    case e of
      { S1 a -> a
      ; S4 -> True
      ; S5 -> False }

-- Comments on skew3 (below)
-- The skew3 function has two equally-plausible maximal types, and
-- Algorithm P infers one of the two types depending on the orientation
-- of the type variable aliasing substitution between the two type
-- arguments of the case scrutinee type.  Here there is no evidence to
-- justify either choice, but in some cases (such as fdComp1) one choice
-- may work a bit better than the other.

skew3 e =
    case e of
      { S1 a -> Just a
      ; S6 -> Nothing }

data D where
  { D1 :: D Int Bool a
  ; D2 :: D (La b) (La c) b }

refine1 e =
    case e of
      { D1 -> (3, True)
      ; D2 -> (C True N, N) }

-- Comments on refine2 (below)
-- The refine2 function demonstrates the importance of propagating type
-- information to the indexing table during the reconcile computation.
-- Without knowing that c=Bool and d=Int, the type inference algorithm
-- cannot decide whether (Just True) should have type (Maybe c) or
-- (Maybe d), and type inference for refine2 would fail.

data E where
  { E1 :: E Int Bool Int Int a b
  ; E2 :: E (La c) (La d) (Maybe c) (Maybe d) c d }

refine2 e =
    case e of
      { E1 -> ((1, True), 3)
      ; E2 -> ((C True N, C 2 N), Just True) }

data G where
  { G1 :: a -> G Int a
  ; G2 :: a -> G Bool a }

-- Comments on param1o (below)
-- The param1o function demonstrates a limitation of Algorithm P in type
-- inference for non-pointwise GADT programs.  The specific limitation
-- that param1o demonstrates is the inability to apply a GADT type
-- refinement to a (scrutinee) type parameter.

param1o e =
    case e of
      { G1 i -> i+3
      ; G2 b -> case b of
                  { True -> 4
                  ; False -> 7 } }

> data G a b where
>     G1 :: a -> G Int a
>     G2 :: a -> G Bool a
> 
> param1 :: G a a -> Int
> param1 (G1 i) = i+3
> param1 (G2 b) = if b then 4 else 7

-- Comments on param2x (below)
-- The param2x function is specially designed to trigger the pattern
-- type escape error on GADT type parameters.  The case expression is
-- ill-typed in the plain GADT type system because the only way to force
-- a=b in the H1 branch is to use the scrutinee type (H (La a) a), which
-- renders the H2 branch unreachable.  Using a constant as the case
-- scrutinee makes the escape undetectable in other parts of the type
-- inference algorithm.

data H where
  { H1 :: La b -> H (La a) b
  ; H2 :: H Int a
  ; H3 :: H a b }

param2x =
    case H3 of
      { H1 b -> b
      ; H2 -> 3 }

--------- Case expressions: Term

data Term where
  { RepInt  :: Int -> Term Int
  ; RepBool :: Bool -> Term Bool
  ; RepCond :: Term Bool -> Term a -> Term a -> Term a
  ; RepSnd  :: Term (a, b) -> Term b
  ; RepPair :: Term a -> Term b -> Term (a, b) }

repId e x =
    case e of
      { RepInt i -> x
      ; RepBool b -> N }

term1 e =
    case e of
      { RepInt i -> i
      ; RepBool b -> b }

term2 e x y =
    case e of
      { RepInt i -> C x y }

-- Comments on term3, term4 (below)
-- The following two examples demonstrate the indexing-averse bias of
-- the type inference algorithm.  This bias works around the lack of
-- principal types in the GADT type system.

term3 e =
    case e of
      { RepInt i -> Just 3
      ; RepBool b -> Nothing }

term4 e x =
    case e of
      { RepInt i -> 3
      ; RepBool b -> x }

term5 e f =
    case e of
      { RepInt i -> f 3
      ; RepBool b -> f True }

term6x e =
    case e of
      { RepInt i -> True
      ; RepBool b -> 3 }

term7 e f =
    case e of
      { RepInt i -> f 3
      ; RepBool b -> f True
      ; RepPair u v -> Nothing }

--------- Nested case expressions

nest1 u =
    case u of
      { Cons x xs -> case xs of
        { Cons y ys -> ys } }

nest2 u v =
    case u of
      { Cons x xs -> case v of
        { Cons y ys -> Just (x, y) }
      ; Nil -> case v of
        { Nil -> Nothing } }

nest3x e =
    case e of
      { Cons x xs -> case e of
        { Nil -> True } }

nest4 e =
    case e of
      { Cons x xs -> case e of
        { Cons y ys -> ys } }

nest5 e =
    case e of
      { Cons x xs -> case xs of
        { Nil -> xs } }

nest6 e =
    case e of
      { Cons x xs -> case xs of
        { Nil -> Nil } }

nest7 e =
    case e of
      { Just a -> case a of
        { RepInt i -> Just i
        ; RepBool b -> Just True }
      ; Nothing -> Nothing }

--------- Application: tagless evaluator

eval1 x =
    case x of
      { RepInt i -> i
      ; RepBool b -> b
      ; RepSnd u -> case eval1 u of
        { (x, y) -> y } }

eval2 x =
    case x of
      { RepInt i -> i
      ; RepBool b -> b
      ; RepPair a b -> (eval2 a, eval2 b) }

eval3 x =
    let { cond a b c = case a of
            { True -> b
            ; False -> c } }
    in case x of
         { RepInt i -> i
         ; RepBool b -> b
         ; RepCond u a b ->
             cond (eval3 u) (eval3 a) (eval3 b) }

eval4 x =
    let { cond a b c = case a of
            { True -> b
            ; False -> c } }
    in case x of
         { RepInt i -> i
         ; RepBool b -> b
         ; RepCond u a b ->
             cond (eval4 u) (eval4 a) (eval4 b)
         ; RepSnd u -> case eval4 u of { (x, y) -> y }
         ; RepPair a b -> (eval4 a, eval4 b) }

--------- Application: length-indexed lists

null e =
    case e of
      { Nil -> True
      ; Cons x xs -> False }

head e =
    case e of
      { Cons x xs -> x }

tail e =
    case e of
      { Cons x xs -> xs }

length l =
    case l of
      { Nil -> 0
      ; Cons x xs -> 1 + length xs }

map f l =
    case l of
      { Nil -> Nil
      ; Cons x xs -> Cons (f x) (map f xs) }

zipWith f a b =
    case a of
      { Nil -> case b of
        { Nil -> Nil }
      ; Cons x xs -> case b of
        { Cons y ys -> Cons (f x y) (zipWith f xs ys) } }

data ExL where
  { ExL :: L n a -> ExL a }

zipWithEx f a b =
    case a of
      { Nil -> ExL Nil
      ; Cons x xs -> case b of
        { Nil -> ExL Nil
        ; Cons y ys -> case zipWithEx f xs ys of
          { ExL zs -> ExL (Cons (f x y) zs) } } }

forget l =
    case l of
      { Nil -> N
      ; Cons x xs -> C x (forget xs) }

isTrue xs =
    let { bin b = case b of
                  { True -> 1
                  ; False -> 0 } }
    in case xs of
         { Nil -> Nil
         ; Cons y ys -> Cons (bin y) (isTrue ys) }

--------- Application: dimensional types

data Deg where
  { Fd :: Int -> Deg F
  ; Kd :: Int -> Deg K
  ; Cd :: Int -> Deg C }

plus a b =
    case a of
      { Fd u -> case b of { Fd v -> Fd (u+v) }
      ; Kd u -> case b of { Kd v -> Kd (u+v) }
      ; Cd u -> case b of { Cd v -> Cd (u+v) } }

kelvin a =
    case a of
      { Kd u -> Kd u
      ; Fd u -> Kd ((u+460)*5/9)
      ; Cd u -> Kd (u+273) }

--------- Application: natural numbers

data Nat where
  { Zn :: Nat Z
  ; Sn :: Nat n -> Nat (S n) }

data NatEqu where
  { EqZ :: NatEqu Z Z
  ; EqS :: NatEqu a b -> NatEqu (S a) (S b) }

data NatLeq where
  { LeZ :: NatLeq Z b
  ; LeS :: NatLeq a b -> NatLeq (S a) (S b) }

> data Z
> data S n
> 
> data Nat a where
>     Zn :: Nat Z
>     Sn :: Nat n -> Nat (S n)
> 
> data NatLeq a b where
>     LeZ :: NatLeq Z b
>     LeS :: NatLeq a b -> NatLeq (S a) (S b)

same k =
    case k of
      { Zn -> EqZ
      ; Sn n -> EqS (same n) }

-- Comments on leq_o (below)
-- Since the second type argument of LeZ is totally unconstrained, the
-- second type argument of the result of leq_o (which is only partially
-- indexed) does not require type indexing to type.  The type inference
-- algorithm chooses the (normally safe) option of foregoing type
-- indexing, which unfortunately in this case creates an infinite type
-- through the recursive reference.

leq_o k =
    case k of
      { Zn -> LeZ
      ; Sn n -> LeS (leq_o n) }

-- Comments on leq1, leq2, leq3 (below)
-- Note that the three functions have the same code but different types
-- representing different theorems about natural numbers.

> leq1 :: Nat n -> NatLeq n n
> leq1 Zn     = LeZ
> leq1 (Sn n) = LeS (leq1 n)
> 
> leq2 :: Nat n -> NatLeq n (S n)
> leq2 Zn     = LeZ
> leq2 (Sn n) = LeS (leq2 n)
> 
> leq3 :: Nat n -> NatLeq n (S (S n))
> leq3 Zn     = LeZ
> leq3 (Sn n) = LeS (leq3 n)

-- Comments on trans_o (below)
-- The trans_o function witnesses the transitivity of natural number
-- less-than-or-equal-to relation.  It presents the same difficulty to
-- the type inference algorithm as in leq_o.

trans_o u v =
    case u of
      { LeZ -> LeZ
      ; LeS w -> case v of
        { LeS r -> LeS (trans_o w r) } }

> trans1 :: NatLeq a b -> NatLeq b c -> NatLeq a c
> trans1 LeZ     _       = LeZ
> trans1 (LeS w) (LeS r) = LeS (trans1 w r)
> 
> trans2 :: NatLeq a b -> NatLeq b c -> NatLeq a (S c)
> trans2 LeZ     _       = LeZ
> trans2 (LeS w) (LeS r) = LeS (trans2 w r)
> 
> trans3 :: NatLeq a b -> NatLeq b c -> NatLeq a (S (S c))
> trans3 LeZ     _       = LeZ
> trans3 (LeS w) (LeS r) = LeS (trans3 w r)

--------- Application: type-equality witness

data Equ where
  { Refl :: Equ a a }

> data Equ a b where
>     Refl :: Equ a a

-- Comments on equ1 (below)
-- Even though this function has an extremely wide range of possible
-- types: Equ a b -> F(a, b) -> F(b, a), where F(x, y) can be any type
-- whose only free type variables are x and y, my type inference
-- algorithm infers only a non-dependent type (i.e., a type that does
-- not use indexing) for equ1.  It is hard to do much better due to the
-- limited expressiveness of the type language.

equ1 e x =
    case e of
      { Refl -> x }

> conv1 :: Equ a b -> a -> b
> conv1 Refl u = u
> 
> conv2 :: Equ a b -> (a, [b]) -> (b, [a])
> conv2 Refl u = u
> 
> conv3 :: Equ (a, Int) (Bool, b) -> (Bool, Int) -> (a, b)
> conv3 Refl u = u

equ2 x y =
    case x of
      { RepInt i -> case y of
        { RepInt j -> Just Refl
        ; RepBool b -> Nothing }
      ; RepBool c -> case y of
        { RepInt j -> Nothing
        ; RepBool b -> Just Refl } }

--------- Application: N-way zip

data Zip1 where
  { Zero1 :: Zip1 (La u) (La u)
  ; Succ1 :: Zip1 (La u) v -> Zip1 (La (w -> u)) (La w -> v) }

-- Comments on zip1o (below)
-- The type inference algorithm infers type indexing by looking for
-- direct contradictions between types, so it fails when there is only
-- an indirect inconsistency.  Here fs has an unknown monomorphic type
-- in the Zero1 branch, which in the Succ1 branch corresponds to both a
-- list type (fs) and a function type (branch body).  Since the
-- contradiction is linked only indirectly through an unknown type in a
-- different branch, the type inference algorithm cannot infer what the
-- unknown type in the Zero1 branch really should be, and type inference
-- for z1 fails as a result.

zip1o n f =
    let { apply f x = f x
        ; repeat x = C x (repeat x)
        ; zipWith f u v = case u of
            { N -> N
            ; C x xs -> case v of
              { N -> N
              ; C y ys -> C (f x y) (zipWith f xs ys) } } } in
    let { z1 n1 fs = case n1 of
            { Zero1 -> fs
            ; Succ1 n2 -> \xs -> z1 n2 (zipWith apply fs xs) } }
    in z1 n (repeat f)

-- Comments on zip1 (below)
-- I tip the type inference algorithm that fs is a list in the Zero1
-- branch by applying fs to the list identity function idLa.  With this
-- little push, the type inference algorithm successfully infers the
-- type of the zip1 function.

zip1 n f =
    let { idLa l = case l of
            { N -> N
            ; C x xs -> C x xs }
        ; apply f x = f x
        ; repeat x = C x (repeat x)
        ; zipWith f u v = case u of
            { N -> N
            ; C x xs -> case v of
              { N -> N
              ; C y ys -> C (f x y) (zipWith f xs ys) } } } in
    let { z1 n1 fs = case n1 of
            { Zero1 -> idLa fs
            ; Succ1 n2 -> \xs -> z1 n2 (zipWith apply fs xs) } }
    in z1 n (repeat f)

data Zip2 where
  { Zero2 :: Zip2 u (La u)
  ; Succ2 :: Zip2 u v -> Zip2 (w -> u) (La w -> v) }

zip2 n f =
    let { z2 = zipS n f z2
        ; zipZ e = case e of
            { Zero2 -> N
            ; Succ2 n -> \ys -> zipZ n }
        ; zipS e f r = case e of
            { Zero2 -> C f r
            ; Succ2 n -> \ys -> case ys of
              { N -> zipZ n
              ; C z zs -> zipS n (f z) (r zs) } } }
    in z2

--------- Application: indexed tree paths

data Path where
  { Here  :: Path Nd
  ; ForkL :: Path x -> Path (Fk x y)
  ; ForkR :: Path y -> Path (Fk x y) }

data Tree where
  { End  :: a -> Tree Nd a
  ; Fork :: Tree u a -> Tree v a -> Tree (Fk u v) a }

find f t =
    let { cond a b c = case a of
            { True -> b
            ; False -> c }
        ; map f l = case l of
            { N -> N
            ; C x xs -> C (f x) (map f xs) }
        ; append x y = case x of
            { N -> y
            ; C u ux -> C u (append ux y) } }
    in case t of
         { End m -> cond (f m) (C Here N) N
         ; Fork x y -> append (map ForkL (find f x))
                              (map ForkR (find f y)) }

extract p t =
    case p of
      { Here -> case t of
        { End m -> m }
      ; ForkL p1 -> case t of
        { Fork x y -> extract p1 x }
      ; ForkR p1 -> case t of
        { Fork x y -> extract p1 y } }

--------- Application: reified state monad

-- Lambda the Ultimate user Pseudonym
-- http://lambda-the-ultimate.org/node/290#comment-2210

data State where
  { Bind   :: State s a -> (a -> State s b) -> State s b
  ; Return :: a -> State s a
  ; Get    :: State s s
  ; Put    :: s -> State s () }

runState e s =
    case e of
      { Return a -> (s, a)
      ; Get      -> (s, s)
      ; Put u    -> (u, ())
      ; Bind m k -> case runState m s of
        { (s1, a1) -> runState (k a1) s1 } }

-- Comments on runState_o (below)
-- The Mycroft type inference semi-algorithm for polymorphic recursion
-- starts by assigning a fully polymorphic type to all recursive
-- references, so the type inference algorithm initially gets no useful
-- type information out of recursive references.  Here, in the inner
-- case expression, the three references to "run" have totoally
-- unrelated types, so the type inference algorithm cannot decide
-- whether s should be indexed to the first or the second type argument
-- of the type of the scrutinee m.

runState_o e s =
    case e of
      { Return a -> (s, a)
      ; Get      -> (s, s)
      ; Put u    -> (u, ())
      ; Bind m k -> case m of
        { Return a -> runState_o (k a) s
        ; Get      -> runState_o (k s) s
        ; Put u    -> runState_o (k ()) u
        ; Bind n j -> runState_o (Bind n (\x -> Bind (j x) k)) s } }

--------- Application: dynamic FRP optimization

data FunDesc where
  { FDI :: FunDesc a a
  ; FDC :: b -> FunDesc a b
  ; FDG :: (a -> b) -> FunDesc a b }

fdFun e =
    case e of
      { FDI   -> \x -> x
      ; FDC b -> \x -> b
      ; FDG f -> f }

-- Comments on fdComp1 (below)
-- The type inference algorithm infers a type for fdComp1 that is less
-- general than expected, and the undesirable behavior is due to a bias
-- in identifying the two range type arguments of FDI (which are both
-- a): the algorithm always considers the first a type index and the
-- second a type argument.  Assuming fd2 has type (FunDesc b c), the
-- algorithm infers the type (FunDesc a c) for both inner references to
-- fd1, which eventually causes b and c to be unified into the same
-- type.  Of course, this arbitrary bias would not have kicked in if the
-- type inference algorithm could establish the relations between fd1
-- and b, and between fd1 and f.  Both b and f are used in a way that
-- suggests that fd1 has type (FunDesc a b), so the type inference
-- algorithm would have made the right call if only it could associate
-- the types of b and f with the type of fd1.

fdComp1 fd1 fd2 =
    let { o f g x = f (g x)
        ; fdFun e = case e of
            { FDI   -> \x -> x
            ; FDC b -> \x -> b
            ; FDG f -> f } }
    in case fd1 of
         { FDI   -> fd2
         ; FDC b -> case fd2 of
           { FDI   -> fd1
           ; FDC c -> FDC ((fdFun fd2) b)
           ; FDG g -> FDC ((fdFun fd2) b) }
         ; FDG f -> case fd2 of
           { FDI   -> fd1
           ; FDC c -> FDC c
           ; FDG g -> FDG (o (fdFun fd2) f) } }

-- Comments on fdComp2 (below)
-- Expanding the two inner references of fd1 to (FDC b) and (FCG f),
-- respectively, allows the type inference algorithm to use the other
-- uses of b and f (e.g., in the inner fd2 FDG branches) to infer an
-- appropriate type for fd1 (and thus for the fdComp2 function).

fdComp2 fd1 fd2 =
    let { o f g x = f (g x)
        ; fdFun e = case e of
            { FDI   -> \x -> x
            ; FDC b -> \x -> b
            ; FDG f -> f } }
    in case fd1 of
         { FDI   -> fd2
         ; FDC b -> case fd2 of
           { FDI   -> FDC b
           ; FDC c -> FDC ((fdFun fd2) b)
           ; FDG g -> FDC ((fdFun fd2) b) }
         ; FDG f -> case fd2 of
           { FDI   -> FDG f
           ; FDC c -> FDC c
           ; FDG g -> FDG (o (fdFun fd2) f) } }

--------- Application: AVL trees

data Avl where
  { Tip   :: Avl Z
  ; LNode :: Avl n     -> Int -> Avl (S n) -> Avl (S (S n))
  ; SNode :: Avl n     -> Int -> Avl n     -> Avl (S n)
  ; MNode :: Avl (S n) -> Int -> Avl n     -> Avl (S (S n)) }

data Ord where
  { LT :: Ord
  ; EQ :: Ord
  ; GT :: Ord }

data E where
  { L :: a -> E a b
  ; R :: b -> E a b }

avltree1 = let
  { compare = undefined
  ; elem i t =
      case t of
        { Tip -> False
        ; LNode a x b -> elem1 i a x b
        ; SNode a x b -> elem1 i a x b
        ; MNode a x b -> elem1 i a x b }
  ; elem1 i a x b =
      case compare i x of
        { EQ -> True
        ; LT -> elem i a
        ; GT -> elem i b }
  ; rotr u v w =
      case u of
        { SNode a x b -> R (LNode a x (MNode b v w))
        ; MNode a x b -> L (SNode a x (SNode b v w))
        ; LNode a x k -> case k of
          { SNode b y c -> L (SNode (SNode a x b) y (SNode c v w))
          ; LNode b y c -> L (SNode (MNode a x b) y (SNode c v w))
          ; MNode b y c -> L (SNode (SNode a x b) y (LNode c v w)) } }
  ; rotl u v w =
      case w of
        { SNode a x b -> R (MNode (LNode u v a) x b)
        ; LNode a x b -> L (SNode (SNode u v a) x b)
        ; MNode k y c -> case k of
          { SNode a x b -> L (SNode (SNode u v a) x (SNode b y c))
          ; LNode a x b -> L (SNode (MNode u v a) x (SNode b y c))
          ; MNode a x b -> L (SNode (SNode u v a) x (LNode b y c)) } }
  ; ins i t =
      case t of
        { Tip -> R (SNode Tip i Tip)
        ; SNode a x b -> case compare i x of
          { EQ -> L t
          ; LT -> case ins i a of
            { L a -> L (SNode a x b)
            ; R a -> R (MNode a x b) }
          ; GT -> case ins i b of
            { L b -> L (SNode a x b)
            ; R b -> R (LNode a x b) } }
        ; LNode a x b -> case compare i x of
          { EQ -> L t
          ; LT -> case ins i a of
            { L a -> L (LNode a x b)
            ; R a -> L (SNode a x b) }
          ; GT -> case ins i b of
            { L b -> L (LNode a x b)
            ; R b -> rotl a x b } }
        ; MNode a x b -> case compare i x of
          { EQ -> L t
          ; LT -> case ins i a of
            { L a -> L (MNode a x b)
            ; R a -> rotr a x b }
          ; GT -> case ins i b of
            { L b -> L (MNode a x b)
            ; R b -> L (SNode a x b) } } }
  } in ()

data Zero where
  { IsZ  :: Zero Z
  ; NotZ :: Zero (S n) }

-- Comments on delmin_o (below)
-- Type inference fails for the delmin_o function, which finds and
-- deletes the smallest element in a tree.  The failure is due to the
-- lack of opposable thumb in the SNode branch: the GADT type argument Z
-- of the subtree b in the IsZ sub-branch is not indexed because there
-- is no mismatching type in the NotZ branch.  (It just so happens that
-- deleting a node in a balanced tree never changes its height.)

avltree2 = let
  { rotl u v w =
      case w of
        { SNode a x b -> R (MNode (LNode u v a) x b)
        ; LNode a x b -> L (SNode (SNode u v a) x b)
        ; MNode k y c -> case k of
          { SNode a x b -> L (SNode (SNode u v a) x (SNode b y c))
          ; LNode a x b -> L (SNode (MNode u v a) x (SNode b y c))
          ; MNode a x b -> L (SNode (SNode u v a) x (LNode b y c)) } }
  ; empty t =
      case t of
        { Tip -> IsZ
        ; LNode a x b -> NotZ
        ; SNode a x b -> NotZ
        ; MNode a x b -> NotZ }
  } in let
  { delmin_o t =
      case t of
        { LNode a x b -> case empty a of
          { IsZ -> (x, L b)
          ; NotZ -> case delmin_o a of
            { (y, k) -> case k of
              { L a -> (y, rotl a x b)
              ; R a -> (y, R (LNode a x b)) } } }
        ; SNode a x b -> case empty a of
          { IsZ -> (x, L b)
          ; NotZ -> case delmin_o a of
            { (y, k) -> case k of
              { L a -> (y, R (LNode a x b))
              ; R a -> (y, R (SNode a x b)) } } }
        ; MNode a x b -> case delmin_o a of
          { (y, k) -> case k of
            { L a -> (y, L (SNode a x b))
            ; R a -> (y, R (MNode a x b)) } } }
  } in ()

--------- Application: Red-Black trees

data RBTree where
  { Root :: RoB Black n -> RBTree }

data RoB where
  { Leaf  :: RoB Black Z
  ; RNode :: RoB Black n -> Int -> RoB Black n -> RoB Red n
  ; BNode :: RoB cL m -> Int -> RoB cR m -> RoB Black (S m) }

data Dir where
  { LeftD  :: Dir
  ; RightD :: Dir }

data Ctxt where
  { BNil  :: Ctxt Black n
  ; RCons :: Int -> Dir -> RoB Black n ->
             Ctxt Red n -> Ctxt Black n
  ; BCons :: Int -> Dir -> RoB c1 n ->
             Ctxt Black (S n) -> Ctxt c n }

-- Sheard gave the following type to this function:
-- recolor :: Dir -> Int -> SubTree Black n ->
--            Dir -> Int -> SubTree Black (S n) ->
--            SubTree Red n -> SubTree Red (S n)

recolor dir1 pE sib dir2 gE uncle t =
    case dir1 of
      { LeftD -> case dir2 of
        { RightD -> RNode (BNode sib pE t) gE uncle
        ; LeftD  -> RNode uncle gE (BNode sib pE t) }
      ; RightD -> case dir2 of
        { RightD -> RNode (BNode t pE sib) gE uncle
        ; LeftD  -> RNode uncle gE (BNode t pE sib) } }

rotate dir1 pE sib dir2 gE uncle tree =
    case tree of
      { RNode x e y -> case dir1 of
        { RightD -> case dir2 of
          { RightD -> BNode (RNode x e y) pE (RNode sib gE uncle)
          ; LeftD  -> BNode (RNode uncle gE x) e (RNode y pE sib) }
        ; LeftD -> case dir2 of
          { RightD -> BNode (RNode sib pE x) e (RNode y gE uncle)
          ; LeftD  -> BNode (RNode uncle gE sib) pE (RNode x e y) } } }

-- Comments on fill_o (below)
-- Type inference for this function fails because some type information
-- is conveyed exclusively through polymorphic recursion.  The tree
-- parameter is sometimes required to be Black (but never Red), so the
-- type inference algorithm decides that tree must always be Black.
-- However, the function does invoke itself recursively with a Red tree
-- as the second argument, so type inference ends with a contradiction.
-- To sum up, the problem here is that the type inference algorithm
-- cannot incorporate type information from recursive references.

fill_o ctx tree =
    case ctx of
      { BNil -> Root tree
      ; RCons e dir uncle c -> case dir of
        { LeftD  -> fill_o c (RNode uncle e tree)
        ; RightD -> fill_o c (RNode tree e uncle) }
      ; BCons e dir uncle c -> case dir of
        { LeftD  -> fill_o c (BNode uncle e tree)
        ; RightD -> fill_o c (BNode tree e uncle) } }

--------- Application: relational algebra

data SortRep where
  { Unary :: SortRep Unary
  ; Tuple :: SortRep Tuple }

data Rep where
  { Int  :: Rep Unary Int
  ; Bool :: Rep Unary Bool
  ; Pair :: Rep Unary a -> Rep x b -> Rep Tuple (a, b) }

data Rep1 where
  { Rep1 :: Rep s t -> SortRep s -> Rep1 t }

pair1 r1 r2 =
    case r1 of
      { Rep1 x t -> case t of
        { Tuple -> undefined
        ; Unary -> case r2 of
          { Rep1 y v -> Rep1 (Pair x y) Tuple } } }

sortOfRep rep =
    case rep of
      { Int -> Unary
      ; Bool -> Unary
      ; Pair x y -> Tuple }

arity rep =
    case rep of
      { Int -> 1
      ; Bool -> 1
      ; Pair x y -> arity x + arity y }

data Literal where
  { IntL     :: Int -> Literal Int
  ; BoolL    :: Bool -> Literal Bool
  ; Wildcard :: Rep Unary t -> Literal t }

literal2Rep lit =
    case lit of
      { IntL i -> Int
      ; BoolL b -> Bool
      ; Wildcard x -> x }

data Crossable where
  { ZeroC :: Crossable t ts (t, ts)
  ; SuccC :: Crossable x y z 
          -> Crossable (a, x) y (a, z) }

-- Comments on crossT_o (below)
-- The type inference algorithm cannot infer a type for crossT_o because
-- the branch types contain no "opposable thumbs", i.e., mismatching
-- type constructors (or types that otherwise fails to unify) that
-- clearly require indexing to specific GADT type arguments.  The lack
-- of opposable thumbs in the branch types may reflect insufficient
-- information in the GADT constructor types.  In the case of Crossable,
-- its types do not state the (implicit) requirement that ts is a Unary
-- type and z is a Tuple type.  Making this requirement explicit may
-- help the type inference algorithm associate branch types to indices.

crossT_o cb x y =
    case cb of
      { ZeroC -> (x, y)
      ; SuccC c -> case x of
        { (a, k) -> (a, crossT_o c k y) } }

data Joinable where
  { ZeroJ :: Joinable t (t, s) s
  ; SuccJ :: Joinable x (t, ts) z
          -> Joinable (y, x) (t, ts) (y, z) }

joinT_o j x y =
    case j of
      { ZeroJ -> case y of
        { (u, v) -> v }
      ; SuccJ j -> case x of
        { (x, xs) -> (x, joinT_o j xs y) } }

