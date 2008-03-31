

-- \begin{verbatim}
--------------------------------------------------------
-- (LE n m) A witness that n is less than or equal to m

prop LE :: Nat ~> Nat ~> *0 where
  Base_LE:: LE Z a
  Step_LE:: LE a b -> LE (S a) (S b)

--------------------------------------------------------
-- A bounded sequence. The elements appear in no
-- particular order, but if a sequence has type 
-- (BSeq min max), every element is between min and max
-- This is maintained by static constraints.

data BSeq :: Nat ~> Nat ~> *0 where
  Nil :: LE min max => BSeq min max
  Cons :: (LE min m, LE m max) => Nat' m -> BSeq min max -> BSeq min max

--------------------------------------------------------
-- helper function for applying one of two functions
-- over a sum type, depending upon the sum injection.

mapP :: (a -> b) -> (c -> d) -> (a+c) -> (b+d)
mapP f g (L x) = L(f x)
mapP f g (R x) = R(g x)

------------------------------------------------------
-- Comparison of two Nat' elements, returns one
-- of two possible witnesses.

compare :: Nat' a -> Nat' b -> (LE a b + LE b a)
compare Z _ = L Base_LE
compare (S x) Z = R Base_LE
compare (S x) (S y) = mapP Step_LE Step_LE (compare x y)

------------------------------------------------------
-- split a Bounded sequence into bounded sequences

qsplit :: (LE min piv, LE piv max) => 
          Nat' piv -> BSeq min max -> (BSeq min piv,BSeq piv max)
qsplit piv Nil = (Nil,Nil)
qsplit piv (Cons x xs) =
    case compare x piv of
      L p1 -> (Cons x small, large)
      R p1 -> (small, Cons x large)
  where (small,large) = qsplit piv xs

------------------------------------------------------
-- A sorted list. Elements are statically guaranteed
-- to appear in ascending order. Note that a list with
-- type (SL min max) has (Nat' min) as first element
-- and every other element less than or equal to max. 
-- Note (Nat' max) may not actually be in the list.

data SL :: Nat ~> Nat ~> *0 where
  SNil :: SL x x
  SCons :: LE min min' => Nat' min -> SL min' max -> SL min max

------------------------------------------------------
-- append two sorted sequences.

app :: SL min piv -> SL piv max -> SL min max
app SNil ys = ys
app (SCons min xs) ys = SCons min (app xs ys)

------------------------------------------------------
-- rearranges a bounded list into a sorted list. Note
-- qsort1 maintains the static invariant that the 
-- first element of the bounded list is less than or
-- equal to the first element of the output.

qsort1 :: BSeq min max -> exists t . LE min t => SL t max
qsort1 Nil = Ex(SNil)
qsort1 (x@(Cons pivot tail)) =  (Ex(app smaller' (SCons pivot larger')))
  where (smaller,larger) = qsplit pivot tail
        (Ex(smaller')) = (qsort1 smaller)
        (Ex(larger')) = (qsort1 larger)

-- \end{verbatim}