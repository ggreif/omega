{-# LANGUAGE ViewPatterns, LambdaCase, RankNTypes #-}

module HuttonBahr where

-- Hutton's razor:

data Exp = Lit Int | Add Exp Exp

-- untransformed evaluator

eval (Lit n) = n
--eval (Add l r) = eval l + eval r
eval (Add (eval -> l) (eval -> r)) = l + r
--eval (Add (eval -> l) ((l+) . eval -> sum)) = sum

-- #############################
-- CPS transform

-- characteristic equality
prop_CPS e eval eval' c = eval' c e == c (eval e)
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
--   "  (eval -> b)   ... (<cont> b)"    ---->      "(<cont> . eval -> b)       ... (b)"
--   "(<cont> . eval -> b)   ... (b)"    ---->      "(flip eval' <cont> -> b)   ... (b)"

-- tackle side "a"...
-- step 0: isolate the continuation c'' of "a"
eval' ((\case Lit n -> n; Add (eval -> a) ((\a' -> flip eval' (a'+)) a -> b) -> b) -> res) c = c res
-- step 1: chain it
eval' ((\case Lit n -> n; Add ((\a' -> flip eval' (a'+)) . eval -> a) (a -> b) -> b) -> res) c = c res
-- step 2: flip it in
-}
eval' ((\case Lit n -> n; Add (flip eval' (\a' -> flip eval' (a'+)) -> a) (a -> b) -> b) -> res) c = c res


-- VICTORY!
