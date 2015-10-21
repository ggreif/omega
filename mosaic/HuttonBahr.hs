{-# LANGUAGE ViewPatterns #-}

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
