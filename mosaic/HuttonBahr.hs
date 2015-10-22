{-# LANGUAGE ViewPatterns, LambdaCase, RankNTypes, GADTs, TemplateHaskell #-}

module HuttonBahr where

-- See: http://www.diku.dk/~paba/pubs/files/hutton15cpsdefun-preprint.pdf
-- for the draft paper.

import Test.QuickCheck

-- Hutton's razor:

data Exp = Lit Int | Add Exp Exp deriving Show

-- untransformed evaluator

eval (Lit n) = n
--eval (Add l r) = eval l + eval r
eval (Add (eval -> l) (eval -> r)) = l + r
--eval (Add (eval -> l) ((l+) . eval -> sum)) = sum

-- #############################
-- CPS transform

-- characteristic equality
pro'p_CPS e eval eval' c = eval' c e == c (eval e)
-- in "left" form
eval'_ c (eval -> res) = c res
-- eval'_ c (c . eval -> res) = res  -- equivalent to above!



{-
{-
eval' :: (Int -> Int) -> Exp -> Int
--eval' c (Lit n) = c n
eval' c (Lit (c -> res)) = res -- considering c as a hypothesis, only usable on the "left"

{-
-- "right" style CPS addition
eval' c (Add x y) === c (eval (Add x y)) === c (eval x + eval y)
-- make it to the form "c' (eval x)" with c' = c . (+ eval y)
=== eval' (c . (+ eval y)) x
-- make "c . (+ eval y)" to the form c'' (eval y) with c'' y' = c . (+y') =?= c . (+)
-- unfortunately "c . (+ eval y)" has type Int -> Int!! so this is not okay
-- so (x' + eval y) to c'' = (x' +) (eval y)
=== eval' (\x' -> c (x' + eval y)) x
=== eval' (\x' -> eval' (c . (x' +)) y) x
-}

eval' c (Add x y) = eval' (\x' -> eval' (c . (x' +)) y) x
-}

-- can we write this in "left" form?
eval' :: Exp -> (Int -> Int) -> Int
Lit n `eval'` c = c n
--Add x y `eval'` c = eval' x (\x' -> eval' y (c . (x' +)))
-- observe: x, y are used linearly as args to eval'
Add (eval' -> ex) (eval' -> ey) `eval'` c = ex (\x' -> ey (c . (x' +))) -- eval' only "left" and guarded!
-- observe: c is used linearly
-- ... -- what can this buy us??


-- can we du a "leftist" derivation too?
--eval' (Lit n) c = c n
-- corresponds to
eval' ((\(Lit a) -> a) -> n) c = c n -- specialization of the
eval' (eval -> n) c = c n -- characteristic "leftist"

-- OKAY so lets use -XLambdaCase to expand the "leftist" characteristic
eval' (eval -> res) c = c res
-- expand eval to lambdacase
eval' ((\case Lit n -> n; Add a b -> eval a + eval b) -> res) c = c res
-- leftist eval
eval' ((\case Lit n -> n; Add (eval -> a) (eval -> b) -> a + b) -> res) c = c res
-- use       eval'_ c' (eval -> b) = c' b      on the "b" side
-- prepare to (c' b) form
eval' ((\case Lit n -> n; Add (eval -> a) (eval -> b) -> (a +) b) -> res) c = c res
-- jump!   (replace linear     "(eval -> b)   ... (<cont> b)" by "(flip eval' <cont> -> b)   ... (b)", effectively moving <cont>)
-}

eval' :: Exp -> (forall k . (Int -> k) -> k)

{-
eval' ((\case Lit n -> n; Add (eval -> a) (flip eval' (a+) -> b) -> b) -> res) c = c res

-- maybe as two steps:
--   "(eval -> b)   ... (<cont> b)"    ---->      "(<cont> . eval -> b)   ... (b)"
--   "(<cont> . eval -> b)   ... (b)"    ---->      "(flip eval' <cont> -> b)   ... (b)"

-- tackle side "a"...
-- step 1: isolate the continuation c'' of "a"
eval' ((\case Lit n -> n; Add (eval -> a) ((\a' -> flip eval' (a'+)) a -> b) -> b) -> res) c = c res
-- step 2: chain it
eval' ((\case Lit n -> n; Add ((\a' -> flip eval' (a'+)) . eval -> a) (a -> b) -> b) -> res) c = c res
-- step 3: flip it in
-}
eval' ((\case Lit n -> n; Add (flip eval' (\a' -> flip eval' (a'+)) -> a) (a -> b) -> b) -> res) c = c res


-- VICTORY!


-- try the same thing for fused CPS-defunctionalisation

-- characteristic equation

type Eval exp = forall k . CONT k -> exp -> k

eval'' :: Eval Exp

{-
eval'' c x = exec c (eval x)   -- compose:       eval'' c x = (exec c . eval) x
                               -- ETA reduce:    eval'' c = exec c . eval          (*)
-- leftise
eval'' c (eval -> res) = exec c res
-- inline eval
eval'' c ((\case Lit n -> n; Add (eval -> a) (eval -> b) -> a + b) -> res) = exec c res
-- observe res is used linearly --> move it's continuation
eval'' c (exec c . (\case Lit n -> n; Add (eval -> a) (eval -> b) -> a + b) -> res') = res'
-- distribute in the arms:
eval'' c ((\case Lit n -> exec c n; Add (eval -> a) (eval -> b) -> exec c (a + b)) -> res') = res'
-- note "b" is used linearly: tackle (eval -> b)
-- find a c' for "  eval'' c' (eval -> b) = exec c' b  =!=  exec c (a + b)  "
-- choose                                   exec c'@(C0 c a) b   := exec c (a + b)
eval'' c ((\case Lit n -> exec c n; Add (eval -> a) (eval -> b) -> exec (C0 c a) b) -> res') = res'
--        note "b" is used linearly here:
--        eval'' c' (eval -> b) = exec c' b
--        eval'' c' (exec c' . eval -> b') = b
eval'' c ((\case Lit n -> exec c n; Add (eval -> a) (exec (C0 c a) . eval -> b') -> b') -> res') = res'
-- use equation (*) backwards
eval'' c ((\case Lit n -> exec c n; Add (eval -> a) (eval'' (C0 c a) -> b') -> b') -> res') = res'

-- GO ON BOLDLY

-- note: "a" used linearly: tackle (eval -> a)
-- find a c'' for "  eval'' c'' (eval -> a) = exec c'' a  =!=  eval'' (C0 c a)  "
-- choose                                     exec c''@(C1 c) a   := eval'' (C0 c a)
eval'' c ((\case Lit n -> exec c n; Add (eval -> a) (exec (C1 c) a -> b') -> b') -> res') = res'
--        note "a" is used linearly here:
--        eval'' c'' (eval -> a) = exec c'' a
--        eval'' c'' (exec c'' . eval -> a') = a'
eval'' c ((\case Lit n -> exec c n; Add (exec (C1 c) . eval -> a') (a' -> b') -> b') -> res') = res'
-- use equation (*) backwards
-}
eval'' c (\case Lit (exec c -> n') -> n'
                Add (eval'' (C1 c) -> a') (a' -> b') -> b'
          -> res') = res'


data CONT k where
  C0 :: CONT k -> Int -> CONT k   -- ADD
  C1 :: CONT k -> CONT (Exp -> k) -- NEXT
  C2 :: CONT Int                  -- HALT

exec :: CONT k -> Int -> k
exec (C0 c a) b = exec c (a + b)
exec (C1 c) a = eval'' (C0 c a)
exec C2 a = a

-- DONE!

instance Arbitrary Exp where
  arbitrary = frequency [ (3, Lit <$> arbitrary)
                        , (2, Add <$> arbitrary <*> arbitrary) ]

prop_eval'' e = eval e === eval'' C2 e

return []
main = $(quickCheckAll)
