-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Tue Jun 12 16:20:11 Pacific Daylight Time 2007
-- Omega Interpreter: version 1.4.2

module Cooper where

{-
This file is based upon an implementation of a Pressburger
arithmetic solver written by John Harrison in OCaml which was
copyright (c) 2003. It was translated to Haskell by Tim Sheard in
2006. As a derivative of that work, it is subject to the following
License in addition to the general Omega license.

--------------------------------------------------------------------
IMPORTANT:  READ BEFORE DOWNLOADING, COPYING, INSTALLING OR USING.
By downloading, copying, installing or using the software you agree
to this license.  If you do not agree to this license, do not
download, install, copy or use the software.

Copyright (c) 2003, John Harrison
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

* Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

* The name of John Harrison may not be used to endorse or promote
products derived from this software without specific prior written
permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
SUCH DAMAGE.
-}

import Char(isDigit)
import List(sortBy,nub)
import Auxillary(plist,plistf,DispElem(..))
import RankN(Tau(..),Pred(..),warnM,TcTv)
import Monads(fio,fio2Mtc)

-- To import ParserAll you must define CommentDef.hs and TokenDef.hs
-- These should be in the same directory as this file.
import ParserAll(Parser,symbol,try,identifier,integer,comma,reserved
                ,parens, sepBy, (<?>), (<|>),parse,parse2,chainl1,many1)

------------------------------------------------
-- from fol.ml

data Term = Var String
          | Fn (String,[Term]) deriving (Eq,Ord)

data Fol = R (String,[Term])
          deriving Eq

{-  There is a bug in this somewhere
instance Ord Term where
  (Var _) < (Fn _) = True
  (Var s) < (Var y) = s<y
  (Fn _) < (Var _) = False
  (Fn(f,xs)) < (Fn(g,ys)) =
     case compare f g of
       EQ -> xs < ys
       LT -> True
       GT -> False

Right(u1,_) = parse2 term "(-1 * z659 + 1 * z605 + 1 * z589 + 1 * z507 + -1)"
Right(u2,_) = parse2 term "(-1 * z659 + 1 * z605 + 1 * z589 + 1 * z507 + 0)"

-- goes into infinite loop, but if I derive Ord for Term we're OK
testu = union [u1] [u2]
-}



fvt (Var x) =  [x]
fvt (Fn(f,args)) = itlist (union . fvt) args []

fv fm =
  case fm of
    FalseF -> []
    TrueF -> []
    Atom(R(p,args)) -> itlist (union . fvt) args []
    Not(p) -> fv p
    And(p,q) -> union (fv p) (fv q)
    Or(p,q) -> union (fv p) (fv q)
    Imp(p,q) -> union (fv p) (fv q)
    Iff(p,q) -> union (fv p) (fv q)
    Forall(x,p) -> subtractSet (fv p) [x]
    Exists(x,p) -> subtractSet (fv p) [x]

------------------------------------------------
-- from lib.ml

earlier :: Eq a => [a] -> a -> a -> Bool
earlier [] x y = False
earlier (h:t) x y =
   if h == y
      then False
      else if h == x
              then True
              else earlier t x y


-- Handy list operations.

-- n (--) m = [n .. m]


-- Merging of sorted lists (maintaining repetitions).

merge ord l1 l2 =
  case l1 of
    [] -> l2
    h1:t1 -> case l2 of
                [] -> l1
                h2:t2 ->  if ord h1 h2
                             then h1:(merge ord t1 l2)
                             else h2:(merge ord l1 t2)

-- Bottom-up mergesort.

sort ord l = if null l then [] else mergepairs [] (map (\ x -> [x]) l)
  where mergepairs l1 l2 =
         case (l1,l2) of
          ([s],[]) -> s
          (l,[]) -> mergepairs [] l
          (l,[s1]) -> mergepairs (s1:l) []
          (l,(s1:s2:ss)) -> mergepairs ((merge ord s1 s2):l) ss

-- Set operations on ordered lists.

setify l = if canonical l then l else nub (sort (<=) l)
  where canonical   (x: rest@(y: _)) = x<y && canonical rest
        canonical _ = True

union s1 s2 = union (setify s1) (setify s2)
  where union l1 l2 =
           case (l1,l2) of
            ([],l2) -> l2
            (l1,[]) -> l1
            (l1@(h1:t1),l2@(h2:t2)) ->
                 if h1 == h2 then h1:(union t1 t2)
                 else if h1 < h2 then h1:(union t1 l2)
                 else h2:(union l1 t2)


subtractSet s1 s2 = sub (setify s1) (setify s2) where
  sub l1 l2 =
    case (l1,l2) of
        ([],l2) -> []
        (l1,[]) -> l1
        (l1@(h1:t1),l2@(h2:t2)) ->
          if h1 == h2 then sub t1 t2
          else if h1 < h2 then h1:(sub t1 l2)
          else sub l1 t2

end_itlist :: Monad m => (b -> b -> b) -> [b] -> m b
end_itlist f l =
 case l of
  []     -> fail "end_itlist"
  [x]    -> return x
  (h:t) -> do { yy <- end_itlist f t; return(f h yy)}

itlist :: (a -> b -> b) -> [a] -> b -> b
itlist f [] b = b
itlist f (h:t) b = f h (itlist f t b)

partition :: (a -> Bool) -> [a] -> ([a],[a])
partition p l =
  itlist (\ a (yes,no) -> if p a then (a:yes,no) else (yes,a:no)) l ([],[])


------------------------------------------------
-- from skolem.ml

-- Routine simplification. Like "psimplify" but with quantifier clauses.

simplify1 fm =
  case fm of
    Forall(x,p) -> if elem x (fv p) then fm else p
    Exists(x,p) -> if elem x (fv p) then fm else p
    _ -> psimplify1 fm

simplify :: Formula Fol -> Formula Fol
simplify fm =
  case fm of
    Not p -> simplify1 (Not(simplify p))
    And(p,q) -> simplify1 (And(simplify p,simplify q))
    Or(p,q) -> simplify1 (Or(simplify p,simplify q))
    Imp(p,q) -> simplify1 (Imp(simplify p,simplify q))
    Iff(p,q) -> simplify1 (Iff(simplify p,simplify q))
    Forall(x,p) -> simplify1(Forall(x,simplify p))
    Exists(x,p) -> simplify1(Exists(x,simplify p))
    _ -> fm

cnnf :: (Formula Fol -> Formula Fol) -> Formula Fol -> Formula Fol
cnnf lfn term = (simplify . help . simplify) term where
 help fm =
    case fm of
      And(p,q) -> And(help p,help q)
      Or(p,q) -> Or(help p,help q)
      Imp(p,q) -> Or(help(Not p),help q)
      Iff(p,q) -> Or(And(help p,help q),And(help(Not p),help(Not q)))
      Not(Not p) -> help p
      Not(And(p,q)) -> Or(help(Not p),help(Not q))
      Not(Or(And(p,q),And(p',r))) | p' == negateF p ->
         Or(help (And(p,Not q)),help (And(p',Not r)))
      Not(Or(p,q)) -> And(help(Not p),help(Not q))
      Not(Imp(p,q)) -> And(help p,help(Not q))
      Not(Iff(p,q)) -> Or(And(help p,help(Not q)),
                          And(help(Not p),help q))
      _ -> lfn fm

cnnfM :: Monad m => (Formula Fol -> m(Formula Fol)) -> Formula Fol -> m(Formula Fol)
cnnfM lfn term = do { x1 <- help(simplify term); return(simplify x1)} where
   help fm =
    case fm of
      And(p,q) -> andM(help p,help q)
      Or(p,q) -> orM(help p,help q)
      Imp(p,q) -> orM(help(Not p),help q)
      Iff(p,q) -> orM(andM(help p,help q), andM(help(Not p),help(Not q)))
      Not(Not p) -> help p
      Not(And(p,q)) -> orM(help(Not p),help(Not q))
      Not(Or(And(p,q),And(p',r))) | p' == negateF p ->
         orM(help (And(p,Not q)),help (And(p',Not r)))
      Not(Or(p,q)) -> andM(help(Not p),help(Not q))
      Not(Imp(p,q)) -> andM(help p,help(Not q))
      Not(Iff(p,q)) -> orM(andM(help p,help(Not q)),
                           andM(help(Not p),help q))
      _ -> lfn fm


------------------------------------------------
-- from formulas.ml

data Formula a
 = FalseF
 | TrueF
 | Atom a
 | Not (Formula a)
 | And (Formula a,Formula a)
 | Or (Formula a,Formula a)
 | Imp (Formula a,Formula a)
 | Iff (Formula a,Formula a)
 | Forall (String,Formula a)
 | Exists (String,Formula a) deriving Eq

andM (x,y) = lift2 And (x,y)
orM (x,y) = lift2 Or (x,y)
notM x = lift1 Not x
impM x = lift2 Imp x
iffM x = lift2 Iff x

onAtoms fn fm =
  case fm of
    Atom(a) -> fn a
    Not(p) -> Not(onAtoms fn p)
    And(p,q) -> And(onAtoms fn p,onAtoms fn q)
    Or(p,q) -> Or(onAtoms fn p,onAtoms fn q)
    Imp(p,q) -> Imp(onAtoms fn p,onAtoms fn q)
    Iff(p,q) -> Iff(onAtoms fn p,onAtoms fn q)
    Forall(x,p) -> Forall(x,onAtoms fn p)
    Exists(x,p) -> Exists(x,onAtoms fn p)
    _ -> fm

onAtomsM fn fm =
  case fm of
    Atom(a) -> fn a
    Not(p) -> lift1 Not(onAtomsM fn p)
    And(p,q) -> lift2 And(onAtomsM fn p,onAtomsM fn q)
    Or(p,q) -> lift2 Or(onAtomsM fn p,onAtomsM fn q)
    Imp(p,q) -> lift2 Imp(onAtomsM fn p,onAtomsM fn q)
    Iff(p,q) -> lift2 Iff(onAtomsM fn p,onAtomsM fn q)
    Forall(x,p) -> lift2 Forall(return x,onAtomsM fn p)
    Exists(x,p) -> lift2 Exists(return x,onAtomsM fn p)
    _ -> return fm


------------------------------------------------
-- from prop.ml

-- Disjunctive normal form (DNF) via truth tables.

list_conj :: [Formula a] -> Formula a
list_conj [] = TrueF
list_conj [x] = x
list_conj (x: xs@(_:_)) = And(x,list_conj xs)

list_disj :: [Formula a] -> Formula a
list_disj [] = FalseF
list_disj [x] = x
list_disj (x: xs@(_:_)) = Or(x,list_disj xs)

--list_disj [] = return FalseF
--list_disj l = end_itlist (\ p q -> Or(p,q)) l

negateF (Not p) = p
negateF p = Not p


-- Routine simplification.

psimplify1 fm =
  case fm of
    Not FalseF -> TrueF
    Not TrueF -> FalseF
    And(FalseF,q) -> FalseF
    And(p,FalseF) -> FalseF
    And(TrueF,q) -> q
    And(p,TrueF) -> p
    Or(FalseF,q) -> q
    Or(p,FalseF) -> p
    Or(TrueF,q) -> TrueF
    Or(p,TrueF) -> TrueF
    Imp(FalseF,q) -> TrueF
    Imp(TrueF,q) -> q
    Imp(p,TrueF) -> TrueF
    Imp(p,FalseF) -> Not p
    Iff(TrueF,q) -> q
    Iff(p,TrueF) -> p
    Iff(FalseF,q) -> Not q
    Iff(p,FalseF) -> Not p
    _ -> fm

psimplify fm =
  case fm of
    Not p -> psimplify1 (Not(psimplify p))
    And(p,q) -> psimplify1 (And(psimplify p,psimplify q))
    Or(p,q) -> psimplify1 (Or(psimplify p,psimplify q))
    Imp(p,q) -> psimplify1 (Imp(psimplify p,psimplify q))
    Iff(p,q) -> psimplify1 (Iff(psimplify p,psimplify q))
    _ -> fm


------------------------------------------------
-- from cooper.ml

--  Lift operations up to numerals.

mk_numeral:: Int -> Term
mk_numeral n = Fn(show n,[])

dest_numeral:: Monad m => Int -> Term -> m Int
dest_numeral n t@(Fn(ns,[])) = if is_numeral t
                                then return (read ns)
                                else fail (show n ++" dest_numeral "++show t)
dest_numeral n t = fail (show n ++" dest_numeral "++ show t)

is_numeral:: Term -> Bool
is_numeral (Fn('-':ns,[])) = all isDigit ns
is_numeral (Fn(ns,[])) = all isDigit ns
is_numeral _ = False

numeral1 :: Monad m => (Int -> Int) -> Term -> m Term
numeral1 fn n = do { m <- dest_numeral 1 n; return(mk_numeral (fn m))}

numeral2 :: Monad m => (Int -> Int -> Int) -> Term -> Term -> m Term
numeral2 fn m n =
  do { a <- dest_numeral 2 m
     ; b <- dest_numeral 3 n
     ; return(mk_numeral (fn a b))}

-- -------------------------------
-- Operations on canonical linear terms c1 * x1 + ... + cn * xn + k          *)
-- Note that we're quite strict: the ci must be present even if 1            *)
-- (but if 0 we expect the monomial to be omitted) and k must be there       *)
-- even if it's zero. Thus, it's a constant iff not an addition term.
-- ------------------------------

linear_cmul :: Monad m => Int -> Term -> m Term
linear_cmul 0 tm = return(Fn("0",[]))
linear_cmul n (Fn("+",[Fn("*",[c1,x1]),rest])) =
  do { zzz <- numeral1 (* n) c1
     ; yyy <- linear_cmul n rest
     ; return(Fn("+",[Fn("*",[zzz, x1]),yyy]))}
linear_cmul n k = numeral1 (* n) k

earlierv :: [String] -> Term -> Term -> Bool
earlierv vars (Var x) (Var y) = earlier vars x y

linear_add :: Monad m => [String] -> Term -> Term -> m Term
linear_add vars tm1@(Fn("+",[Fn("*",[c1, x1]), rest1]))
                tm2@(Fn("+",[Fn("*",[c2, x2]), rest2])) =
  do { c <- numeral2 (+) c1 c2
     ; if x1 == x2
          then do { tail <- linear_add vars rest1 rest2
                  ; case c of
                      Fn("0",[]) -> return tail
                      c -> return(Fn("+",[Fn("*",[c, x1]), tail]))}
          else if earlierv vars x1 x2
                  then do { tail <- linear_add vars rest1 tm2
                          ; return(Fn("+",[Fn("*",[c1, x1]), tail]))}
                  else do { tail <- linear_add vars tm1 rest2
                          ; return(Fn("+",[Fn("*",[c2, x2]), tail]))}}
linear_add vars tm1@(Fn("+",[Fn("*",[c1, x1]), rest1])) tm2 =
  do { tail <- linear_add vars rest1 tm2
     ; return( Fn("+",[Fn("*",[c1, x1]), tail]))}
linear_add vars tm1 tm2@(Fn("+",[Fn("*",[c2, x2]), rest2])) =
  do { tail <- linear_add vars tm1 rest2
     ; return(  Fn("+",[Fn("*",[c2, x2]), tail]) )}
linear_add vars tm1 tm2 = numeral2 (+) tm1 tm2

linear_neg :: Monad m => Term -> m Term
linear_neg tm = linear_cmul (-1) tm

linear_sub :: Monad m => [String] -> Term -> Term -> m Term
linear_sub vars tm1 tm2 =
  do { tm2' <- linear_neg tm2
     ; linear_add vars tm1 tm2'}

-------------------------------
-- Linearize a term.
-------------------------------

lint :: Monad m => [String] -> Term -> m Term
lint vars tm@(Var x) = return (Fn("+",[Fn("*",[Fn("1",[]), tm]), Fn("0",[])]))
lint vars (Fn("-",[t])) = do { t2 <- (lint vars t); linear_neg t2}
lint vars (Fn("+",[s,t])) =
   do { s' <- lint vars s; t' <- lint vars t; linear_add vars s' t'}
lint vars (Fn("-",[s,t])) =
   do { s' <- lint vars s; t' <- lint vars t; linear_sub vars s' t'}
lint vars (Fn("*",[s,t])) =
   do { s' <- lint vars s
      ; t' <- lint vars t
      ; if is_numeral s'
           then do { c <- dest_numeral 4 s'; linear_cmul c t'}
           else if is_numeral t'
                   then do { c <- dest_numeral 5 t'; linear_cmul c s'}
                   else fail "lint: apparent nonlinearity"}
lint vars tm =
  if is_numeral tm
     then return tm
     else fail "lint: unknown term"

-------------------------------------------------------------------------
-- Linearize the atoms in a formula, and eliminate non-strict inequalities.
-------------------------------------------------------------------------

mkatom vars p t = do { zz <- lint vars t;
                     ; return (Atom(R(p,[Fn("0",[]),zz])))}


linform :: Monad m => [String] -> Formula Fol -> m (Formula Fol)
linform vars (Atom(R("divides",[c,t]))) =
  do { yy <- lint vars t
     ; c2 <- dest_numeral 6 c
     ; let c' = mk_numeral(abs c2)
     ; return( Atom(R("divides",[c', yy])) )}
linform vars (Atom(R("=",[s,t]))) = mkatom vars "=" (Fn("-",[t,s]))
linform vars (Atom(R("<",[s,t]))) = mkatom vars "<" (Fn("-",[t,s]))
linform vars (Atom(R(">",[s,t]))) = mkatom vars "<" (Fn("-",[s,t]))
linform vars (Atom(R("<=",[s,t]))) =
  mkatom vars "<" (Fn("-",[Fn("+",[t,Fn("1",[])]),s]))
linform vars (Atom(R(">=",[s,t]))) =
  mkatom vars "<" (Fn("-",[Fn("+",[s,Fn("1",[])]),t]))
linform vars fm = return fm

--------------------------------------------------------------
-- Post-NNF transformation eliminating negated inequalities.
--------------------------------------------------------------

posineq :: Monad m => Formula Fol -> m (Formula Fol)
posineq fm@(Not(Atom(R("<",[Fn("0",[]), t])))) =
  do { zz <-  linear_sub [] (Fn("1",[])) t
     ; return( Atom(R("<",[Fn("0",[]), zz])) )}
posineq fm = return fm

-------------------------------------------------
-- Find the LCM of the coefficients of x.
-------------------------------------------------

formlcm :: Monad m => Term -> Formula Fol -> m Int
formlcm x fm@(Atom(R(p,[_,Fn("+",[Fn("*",[c,y]),z])]))) | y == x =
  do { n <- dest_numeral 7 c; return (abs n)}
formlcm x fm@(Not(p)) =  formlcm x p
formlcm x fm@(And(p,q)) =
  do { a <- formlcm x p; b <- formlcm x q; return(lcm a b)}
formlcm x fm@(Or(p,q)) =
  do { a <- formlcm x p; b <- formlcm x q; return(lcm a b)}
formlcm x fm = return 1

------------------------------------------------------------------------
-- Adjust all coefficients of x in formula; fold in reduction to +/- 1.
------------------------------------------------------------------------

lift1 f x = do { a <- x; return(f a) }
lift2 f (x,y) = do { a <- x; b <- y; return(f (a,b))}

adjustcoeff :: Monad m => Term -> Int -> Formula Fol -> m (Formula Fol)
adjustcoeff x l fm@(Atom(R(p,[d, Fn("+",[Fn("*",[c,y]),z])]))) | y == x =
  do { c1 <- dest_numeral 8 c
     ; let m = l `div` c1
           n = if p == "<" then abs(m) else m
           xtm = Fn("*",[mk_numeral(m `div` n), x])
     ; xx <- linear_cmul (abs m) d
     ; yy <- linear_cmul n z
     ; return( Atom(R(p,[xx,Fn("+",[xtm,yy])])) )}
adjustcoeff x l fm@(Not(p)) = lift1 Not(adjustcoeff x l p)
adjustcoeff x l fm@(And(p,q)) = lift2 And(adjustcoeff x l p,adjustcoeff x l q)
adjustcoeff x l fm@(Or(p,q)) =  lift2 Or(adjustcoeff x l p,adjustcoeff x l q)
adjustcoeff x l fm = return fm

----------------------------------------------------------------
-- Hence make coefficient of x one in existential formula.
----------------------------------------------------------------

unitycoeff x fm =
  do { l <- formlcm x fm
     ; fm' <- adjustcoeff x l fm
     ; if l == 1
          then return fm'
          else do { yy <- adjustcoeff x l fm
                  ; let xp = Fn("+",[Fn("*",[Fn("1",[]),x]), Fn("0",[])])
                  ; return(And(Atom(R("divides",[mk_numeral l, xp])),yy)) }}

--------------------------------
-- The "minus infinity" version.
--------------------------------

minusinf x fm =
  case fm of
    Atom(R("=",[Fn("0",[]), Fn("+",[Fn("*",[Fn("1",[]),y]),z])]))
        | y == x -> FalseF
    Atom(R("<",[Fn("0",[]), Fn("+",[Fn("*",[pm1,y]),z])])) | y == x ->
        if pm1 == Fn("1",[]) then FalseF else TrueF
    Not(p) -> Not(minusinf x p)
    And(p,q) -> And(minusinf x p,minusinf x q)
    Or(p,q) -> Or(minusinf x p,minusinf x q)
    _ -> fm

----------------------------------------------
-- The LCM of all the divisors that involve x.
----------------------------------------------

-- a curried version of lift2
liftC f x y = do { a <- x; b <- y; return(f a b)}

divlcm :: Monad m => Term -> Formula Fol -> m Int
divlcm x fm =
  case fm of
    Atom(R("divides",[d,Fn("+",[Fn("*",[c,y]),z])])) | y == x ->
        dest_numeral 9 d
    Not(p) -> divlcm x p
    And(p,q) -> liftC lcm (divlcm x p) (divlcm x q)
    Or(p,q) -> liftC lcm (divlcm x p) (divlcm x q)
    _ -> return 1

----------------------------
-- Construct the B-set.
----------------------------

one x = [x]

bset x fm =
  case fm of
    Not(Atom(R("=",[Fn("0",[]), Fn("+",[Fn("*",[Fn("1",[]),y]),a])])))
       | y==x -> do { ww <- (linear_neg a)
                    ; return [ww]}
    Atom(R("=",[Fn("0",[]), Fn("+",[Fn("*",[Fn("1",[]),y]),a])]))
       | y==x -> do { yy <- linear_add [] a (Fn("1",[]))
                    ; zz <- linear_neg(yy)
                    ; return[zz]}
    Atom(R("<",[Fn("0",[]), Fn("+",[Fn("*",[Fn("1",[]),y]),a])]))
       | y==x -> lift1 one (linear_neg a)
    Not(p) -> bset x p
    And(p,q) -> do { ps <- (bset x p)
                   ; qs <- (bset x q)
                   ;return (union ps qs)}
    Or(p,q) ->  liftC union (bset x p) (bset x q)
    _ -> return []

-------------------------------------------------------------------------
-- Replace top variable with another linear form, retaining canonicality.
-------------------------------------------------------------------------

linrep vars x t fm =
  case fm of
    Atom(R(p,[d, Fn("+",[Fn("*",[c,y]),z])])) | y==x ->
        do { c1 <- dest_numeral 10 c
           ; ct <-  linear_cmul c1 t
           ; yy <- linear_add vars ct z
           ; return(Atom(R(p,[d, yy])))}
    Not(p) ->  lift1 Not(linrep vars x t p)
    And(p,q) -> lift2 And(linrep vars x t p,linrep vars x t q)
    Or(p,q) -> lift2 Or(linrep vars x t p,linrep vars x t q)
    _ -> return fm


--------------------------------------------
-- Evaluation of constant expressions.
--------------------------------------------

operations :: [(String,Int -> Int -> Bool)]
operations =
  [("=",(==)), ("<",(<)), (">",(>)), ("<=",(<=)), (">=",(>=)),
   ("divides",\ x y -> mod y x == 0)]


evalc_atom :: Fol -> Formula Fol
evalc_atom at@(R(p,[s,t]))
  = case lookup p operations of
      Nothing -> Atom at
      Just f -> case (dest_numeral 11 s,dest_numeral 12 t) of
                  (Just a, Just b) -> if (f a b) then TrueF else FalseF
                  other -> Atom at
evalc_atom at = (Atom at)


evalc :: Formula Fol -> Formula Fol
evalc x = onAtoms evalc_atom x;

-----------------------------------------------------
-- Hence the core quantifier elimination procedure.
-----------------------------------------------------

cooper vars fm@(Exists(x0,p0)) =
 do { let x = Var x0
    ; p <- unitycoeff x p0
    ; let p_inf = simplify(minusinf x p)
    ; bs <- bset x p
    ; nn <- divlcm x p
    ; let js = [1 .. nn]
          p_element j b =
             do { yy <- linear_add vars b (mk_numeral j)
                ; linrep vars x yy p}
          stage j =
             do { xx <- linrep vars x (mk_numeral j) p_inf
                ; ys <- mapM (p_element j) bs
                ; return(list_disj(xx:ys))}
    ; zs <- mapM stage js
    ; return(list_disj zs) }
cooper vars fm = fail "cooper: not an existential formula"


----------------------
-- Overall function.
----------------------

-- integer_qelim :: Monad a => Formula Fol -> a (Formula Fol)
integer_qelim term =
  do { let normform x = cnnfM posineq (evalc x)
     ; term1 <- linform (fv term) term
     ; term2 <- lift_qelimM linform normform cooper term1
     ; return(simplify (evalc term2))
     }

---------------------------------------------------
-- from qelim.ml

disjuncts (Or(p,q)) = disjuncts p ++ disjuncts q
disjuncts x = [x]

conjuncts (And(p,q)) = conjuncts p ++ conjuncts q
conjuncts x = [x]


-- Lift procedure given literal modifier, formula normalizer, and a  basic
-- elimination procedure for existential formulas with conjunctive body.

lift_qelim :: ([String] -> Formula Fol -> Formula Fol) ->
              (Formula Fol -> Formula Fol) ->
              ([String] -> Formula Fol -> Formula Fol) ->
              Formula Fol ->
              Formula Fol

lift_qelim afn nfn qfn fm = simplify(qelift (fv fm) fm) where
  qelift vars fm =
    case fm of
      Atom(R(_,_)) -> afn vars fm
      Not(p) -> Not(qelift vars p)
      And(p,q) -> And(qelift vars p,qelift vars q)
      Or(p,q) -> Or(qelift vars p,qelift vars q)
      Imp(p,q) -> Imp(qelift vars p,qelift vars q)
      Iff(p,q) -> Iff(qelift vars p,qelift vars q)
      Forall(x,p) -> Not(qelift vars (Exists(x,Not p)))
      Exists(x,p) ->
          let djs = disjuncts(nfn(qelift (x:vars) p)) in
          list_disj(map (qelim x vars) djs)
      _ -> fm
  qelim x vars p =
    let cjs = conjuncts p
        (ycjs,ncjs) = partition (elem x . fv) cjs
    in if null ycjs
          then p
          else let q = qfn vars (Exists(x,list_conj ycjs))
               in foldr (\ p q -> And(p,q)) q ncjs

-- A monadic version

{-
lift_qelimM :: Monad m =>
              ([String] -> Formula Fol -> m(Formula Fol)) ->
              (Formula Fol -> m(Formula Fol)) ->
              ([String] -> Formula Fol -> m(Formula Fol)) ->
              Formula Fol ->
              m(Formula Fol)
-}

waitQ = putStrLn "return to continue" >> (getLine)

lift_qelimM afn nfn qfn fm = do {x <- qelift (fv fm) fm
                                ; return(simplify x)} where
  qelift vars fm =
    case fm of
      Atom(R(_,_)) -> afn vars fm
      Not(p) -> notM(qelift vars p)
      And(p,q) -> andM(qelift vars p,qelift vars q)
      Or(p,q) -> orM(qelift vars p,qelift vars q)
      Imp(p,q) -> impM(qelift vars p,qelift vars q)
      Iff(p,q) -> iffM(qelift vars p,qelift vars q)
      Forall(x,p) -> notM(qelift vars (Exists(x,Not p)))
      Exists(x,p) ->
          do { p1 <- qelift (x:vars) p
             ; p2 <- nfn p1
             ; let djs = disjuncts p2
             ; djs2 <- mapM (qelim x vars) djs
             ; return(list_disj djs2)}
      _ -> return fm
  qelim x vars p =
    let cjs = conjuncts p
        (ycjs,ncjs) = partition (elem x . fv) cjs
    in if null ycjs
          then return p
          else do { q <- qfn vars (Exists(x,list_conj ycjs))
                  ; return (foldr (\ p q -> And(p,q)) q ncjs)}

-----------------------------------------------------------------
-- Parsing

oneOf p [] = fail "oneOf"
oneOf p (s:ss) = (try (p s)) <|> oneOf p ss

lit :: Parser Term
lit =
  do {n <- integer; return(mk_numeral(fromInteger n))}

var:: Parser Term
var =
  do { x <- identifier; return(Var x)}

factor:: Parser Term
factor =
       lit
   <|> var
   <|> parens term


prod:: Parser Term
prod = chainl1 factor (symbol "*" >> return times)
  where times x y = Fn("*",[x,y])

term:: Parser Term
term = chainl1 prod oper
  where op name x y = Fn(name,[x,y])
        oper = do { x <- oneOf symbol ["+","-"]
                  ; return(op x)}

rel:: Parser (Formula Fol)
rel = (try (symbol "true" >> return TrueF)) <|>
      (try (symbol "false" >> return FalseF)) <|>
      (try quant) <|>
      (try (do { symbol "~"; x <- rel; return(Not x)})) <|>
      (parens form) <|>
      (do { x <- term         -- always put those which are prefixes later
          ; f <- oneOf symbol ["=","/=","<=","<",">=",">"]
          ; y <- term
          ; case f of
             "/=" -> return(Not(Atom(R("=",[x,y]))))
             op -> return(Atom(R(f,[x,y])))})

keyword s = reserved s >> return s

quant:: Parser (Formula Fol)
quant = do { f <- oneOf symbol ["exists","forall"]
           ; vs <- many1 identifier
           ; symbol "."
           ; body <- form
           ; case f of
               "exists" -> return(exF vs body)
               "forall" -> return(allF vs body)}

exF [] body = body
exF (v:vs) body = Exists(v,exF vs body)
allF [] body = body
allF (v:vs) body = Forall(v,allF vs body)

form:: Parser (Formula Fol)
form = (chainl1 rel oper)
  where op "&&" x y = And(x,y)
        op "||" x y = Or(x,y)
        op "==>" x y = Imp(x,y)
        op "<=>" x y = Iff(x,y)
        oper = do { x <- (symbol "&&") <|> (symbol "||") <|>
                         (symbol "==>") <|> (symbol "<=>")
                  ; return(op x)}


go s = parse2 form s

--------------------------------------------------------------------
-- showing formula

plusP (Fn("+",_)) = True
plusP (Fn("-",_)) = True
plusP _ = False

showp p x = if p x then "("++show x++")" else show x

instance Show Term where
  show (Var s) = s
  show (Fn("+",[x,y]))  = show x ++ " + " ++ show y
  show (Fn("-",[x,y]))  = show x ++ " - " ++ show y
  show (Fn("*",[x,y]))  = showp plusP x ++ " * " ++ showp plusP y
  show (Fn("=",[x,y]))  = show x ++ " = " ++ show y
  show (Fn("/=",[x,y])) = show x ++ " /= " ++ show y
  show (Fn("<",[x,y]))  = show x ++ " < " ++ show y
  show (Fn("<=",[x,y])) = show x ++ " <= " ++ show y
  show (Fn(">",[x,y]))  = show x ++ " > " ++ show y
  show (Fn(">=",[x,y])) = show x ++ " >= " ++ show y
  show (Fn('-':xs,_)) | all isDigit xs = "-"++xs
  show (Fn(x,[])) | all isDigit x = x
  show (Fn(f,xs)) = plist (f++"(") xs "," ")"

instance Show Fol where
  show (R(x,y)) = show (Fn(x,y))

gNot (Forall _ ) = False
gNot (Exists _) = False
gNot (Atom(R(_,[]))) = False
gNot (Atom(R _)) = True
gNot (Not _) = False
gNot _ = True

gAnd (And _ ) = False
gAnd x = gNot x

gOr (Or _) = False
gOr x = gAnd x

gImp (Imp _) = False
gImp x = gOr x

gIff (Iff _) = False
gIff x = gImp x


instance Show (Formula Fol) where
  show form =
    case form of
      TrueF -> "true"
      FalseF -> "false"
      Atom(x) -> show x
      Not(p) -> "~"++ showp gNot p
      And(p,q) -> showp gAnd p ++ " && "++showp gAnd q
      Or(p,q) ->  showp gOr p ++ " || "++showp gOr q
      Imp(p,q) -> showp gImp p ++ " ==> "++showp gImp q
      Iff(p,q) -> showp gIff p ++ " <=> "++showp gIff q
      Forall(x,p) -> let (vs,p) = allVs [] form
                     in "(forall "++plistf id "" vs " " ". "++show p++")"
      Exists(x,p) -> let (vs,p) = exVs [] form
                     in "(exists "++plistf id "" vs " " ". "++show p++")"

exVs xs (Exists(x,body)) = exVs (x:xs) body
exVs xs body = (reverse xs,body)

allVs xs (Forall(x,body)) = allVs (x:xs) body
allVs xs body = (reverse xs,body)

-------------------------------------------------------------------

readForm s = case parse2 form s of
           Right(x,[])-> putStrLn (show x) >> return x
           Right(x,more) -> putStrLn ("Unconsumed input: "++more) >> return FalseF
           Left s -> putStrLn ("Parse error: "++ s) >> return FalseF

test s =
  do { form <- readForm s
     ; ans <- integer_qelim form
     ; putStrLn (show ans)
     ; return (form,ans)}

ex1 = test "forall x y. x < y ==> 2 * x + 1 < 2 * y"

ex2 = test "forall x y. ~(2 * x + 1 = 2 * y)"

ex3 = test "exists x y. x > 0 && y >= 0 && 3 * x - 5 * y = 1"

ex4 = test "exists x y z. 4 * x - 6 * y = 1"

ex5 = test "forall x. b < x ==> a <= x"

ex6 = test "forall x. a < 3 * x ==> b < 3 * x"

ex7 = test "forall x y. x <= y ==> 2 * x + 1 < 2 * y"

ex8 = test "(exists d. y = 65 * d) ==> (exists d. y = 5 * d)"

ex9 = test
  "forall y. (exists d. y = 65 * d) ==> (exists d. y = 5 * d)"

ex10 = test "forall x y. ~(2 * x + 1 = 2 * y)"

ex11 = test
  "forall x y z. (2 * x + 1 = 2 * y) ==> x + y + z > 129"

ex12 = test "forall x. a < x ==> b < x"

ex13 = test "forall x. a <= x ==> b < x"

ex14 = test "forall x. (exists y. x = 2*y) && (exists y. x = 3*y) ==> (exists y. x = 6*y)"

set1 = [ex1,ex2,ex3,ex4,ex5,ex6,ex7,ex8,ex9,ex10,ex11,ex12,ex13,ex14]


ex00 = test $
  "forall a b c d e f."++
     "(1 + e + 1 + f = a + 1 + b) && "++
     "(e + 1 + f = c + 1 + d) ==> (a + b = 1 + c + d)"


ex20 = test "forall n. exists m w. n+n = 2+m ==> (n = w+1 && m = w+w)"

exhalf = test "forall n m w . (n+n = 2+m) && (n = w+1) ==> (m = w+w)"

--------------------------------------------

ex15 = test "(z1900 + 0 + 0 = z1900 + 0) && (z1890 + z1900 + 0 + z1900 + 0 = z1738 + z1820 + z1836) ==> (z1890 + z1900 + z1824 + z1840 + z1900 + z1824 + z1840 = z1738 + z1820 + z1824 + z1824 + z1836 + z1840 + z1840)"
-- ripple carry adder example

next = do { (a,b) <- ex15
          ; let b2 = universal b
          ; putStrLn (show b2)
          ; case  (Just b2) of --integer_qelim b2 of
             Just as -> putStrLn (show as)
             Nothing -> putStrLn "Ooops"
          ; return ()
          }

ss = ("forall z507 z589 z593 z605 z609 z659 z669. (z669 + 0 = z669 + 0) "++
      "&& (z659 + z669 + 0 + z669 + 0 = z507 + z589 + z605) ==> "++
      "(z659 + z669 + z593 + z609+ z669 + z593 + z609 = "++
      "z507 + z589 + z593 + z593 + z605 + z609 + z609)")

ex16 = test ss

-----------------------------------------------------------------

universal form = allF all_vs (exF ex_vs form)
  where total_vs = (fv form)
        universal ('_':xs) = True
        universal x = False
        (all_vs,ex_vs) = partition universal total_vs


type Map = [(TcTv,String)]

tauTerm:: Map -> Tau -> Maybe Term
tauTerm env v@(TcTv x) =
    case lookup x env of
       Nothing -> Just(Var(show v))
       Just s -> Just(Var s)
tauTerm env (TyFun "plus" k [x,y]) =
   do { a <- tauTerm env x
      ; b <- tauTerm env y
      ; return(Fn("+",[a,b]))}
tauTerm env (TyFun "times" k [x,y]) =
   do { a <- tauTerm env x
      ; b <- tauTerm env y
      ; return(Fn("*",[a,b]))}
tauTerm env (TyCon sx lev "Z" k) = return(mk_numeral 0)
tauTerm env (TyApp (TyCon sx _ "S" k) x) =
   do { x2 <- tauTerm env x
      ; case x2 of
          x | is_numeral x ->
               do { n <- dest_numeral 0 x; return(mk_numeral(n+1))}
          (Fn("+",[y,x])) | is_numeral y ->
               do { n <- dest_numeral 0 y; return(Fn("+",[mk_numeral(n+1),x]))}
          x -> return(Fn("+",[mk_numeral 1,x]))}
tauTerm env x = Nothing

predForm:: Map -> Pred -> Maybe Term
predForm env (Equality x y) =
  do { a <- tauTerm env x
     ; b <- tauTerm env y
     ; return(Fn("=",[a,b]))}
predForm env (Rel _) = Nothing

toForm (Fn(f,xs)) = Just(R(f,xs))
toForm _ = Nothing


toF:: Map -> Tau -> Maybe [Formula Fol]
toF env (TyFun "and" _ [x,y]) =
  do { x' <- toF env x
     ; y' <- toF env y
     ; return(x' ++ y')}
toF env (TyApp  (TyApp (TyCon sx _ "Equal" _) lhs) rhs) =
  do { lhsterm <- tauTerm env lhs
     ; rhsterm <- tauTerm env rhs
     ; return [Atom(R("=",[lhsterm,rhsterm]))] }

toFormula:: Map -> [(Tau,Tau)] -> Tau -> Maybe (Formula Fol,Formula Fol)
toFormula env truths concl =
  do { terms <- mapM (predForm env) (map (uncurry Equality) truths)
     ; fols <- mapM toForm terms
     ; let hyp = (map Atom fols)
     ; body <- toF env concl
     ; let (prefix,tail ) = case body of
                             [x] -> ([],x)
                             xs -> (init xs,last xs)
     ; let formula = (Imp(list_conj(hyp++prefix),tail))
     ; return (universal formula,formula) }






