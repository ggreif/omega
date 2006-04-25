-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Tue Apr 25 12:54:27 Pacific Daylight Time 2006
-- Omega Interpreter: version 1.2.1

module Syntax where

import Bind
import Monad
import Monads
import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import Auxillary
import List(elem,nub,union,(\\),partition,find)
import RankN(PT(..),showp,getAll,getFree,getFreePredL,applyT',ptsub,ppredsub
            ,getMult,PPred(..))
import Char(isLower,isUpper)
import Pretty

-- To import ParserAll you must define CommentDef.hs and TokenDef.hs
-- These should be in the same directory as this file.

import ParserAll(Parser)

-- By rights these should be defined in Value.hs But then
-- we'd have recursive import lists

data Ev = Ev [(Var,V)] (V,V,V)

showenv (Ev xs m) =
  "Ev with \n   "++show (map fst xs)

type EnvFrag = [(Var,V)]

data V
  = Vlit Lit
  | Vsum Inj V
  | Vprod V V
  | Vprimfun String (V -> FIO V)
  | Vfun [Pat] Exp Ev
  | Vf (V -> FIO V) (Ev -> V) (Perm -> V)
  | Vcon Var [V]
  | Vpat Var ([Pat]->Pat) V
  | Vlazy Perm (IORef (Either (FIO V) V))
  | Vcode Exp Ev
  | Vswap Perm V
  | Vfio Perm (FIO (Either String V))
  | Vptr Perm Integer (IORef (Maybe V))
  | VChrSeq String
  | Vparser (Parser V)
  | Vbottom


-----------------------------------------------
-- Var represents variables. There are two kinds
-- Global, used to represent top-level declarations
-- and Alpha, used to represent alpha-renamable variables.

data Var
  = Global String        -- Global Names
  | Alpha String Name    -- Alpha renamable Names

var s = Var (Global s)

instance Eq Var where
  (Global x) == (Global y) = x==y
  (Alpha _ x) == (Alpha _ y) = x==y
  _ == _ = False

instance Ord Var where
  compare (Global s) (Alpha nm n) =  LT
  compare (Alpha nm n) (Global s) = GT
  compare (Alpha _ n) (Alpha _ m) = compare n m
  compare (Global n) (Global m) = compare n m

instance Show Var where
   show (Global s) = s
   show (Alpha x nm) = x++ tail(show nm)

instance Freshen Var where
  freshen (Global s) = return(Global s,[])
  freshen (Alpha s nm) = do { nm' <- fresh; return(Alpha s nm',[(nm,nm')])}

instance Swap Var where
  swaps [] v = v
  swaps cs (Global s) = Global s
  swaps cs (Alpha s nm) = Alpha s (swaps cs nm)

---------------------------------------------------
type Targs = [(Var,PT)]

data Lit
  = Int Int
  | Char Char
  | Unit
  | Symbol Name
  | ChrSeq String
  | Tag String
  | Float Float

data Inj = L | R deriving (Eq,Show)

data Pat
  = Plit Lit                  -- { 5 or 'c' }
  | Pvar Var                  -- { x }
  | Pprod Pat Pat             -- { (p1,p2) }
  | Psum Inj Pat              -- { L p   or   R p  }
  | Pexists Pat               -- { Ex p }
  | Paspat Var  Pat           -- { x @ p }
  | Pwild                     -- { _ }
  | Pcon Var [Pat]            -- C x y (z,a)
  | Pann Pat PT               -- p :: t

data Exp
  = Var Var                   -- { x }
  | Lit Lit                   -- { 5 or 'c'}
  | Sum Inj Exp               -- { L x  or  R y }
  | Prod Exp Exp              -- { (e1,e2) }
  | App Exp Exp               -- { f x }
  | Lam [Pat] Exp [(Var,Int)] -- { \ p1 p2 -> e }
  | Let [Dec] Exp             -- { let x=e1;   y=e2 in e3 }
  | Circ [Var] Exp [Dec]      -- { circuit e where x = e1; y = 32 }
  | Case Exp [Match Pat Exp Dec]  -- { case e of m1; m2 }
  | Do [Stmt Pat Exp Dec]     -- { do { p <- e1; e2 }  }
  | CheckT Exp
  | Lazy Exp
  | Exists Exp
  | Under Exp Exp
  | Bracket Exp
  | Escape Exp
  | Run Exp
  | Reify String V
  | Ann Exp PT

type Match p e d = (Loc,p,Body e,[d]) -- case e of { p -> b where decs }

data Body e
  = Guarded [(e,e)]           -- f p { | e1 = e2 | e3 = e4 } where ds
  | Normal e                  -- f p = { e } where ds
  | Unreachable

data Stmt p e d
  = BindSt Loc p e
  | LetSt Loc [ d ]
  | NoBindSt Loc e

data Dec
  = Fun Loc Var (Maybe PT) [Match [Pat] Exp Dec]   -- { f p1 p2 = b where decs }
  | Val Loc Pat (Body Exp) [Dec]        -- { p = b where decs }
  | Pat Loc Var [Var] Pat               -- { Let x y z = App (Lam x z) y
  | TypeSig Loc Var PT                  -- { id :: a -> a }
  | Prim Loc Var PT                     -- { prim bind :: a -> b }
  | Data Loc Bool Strata Var (Maybe PT) Targs [Constr][Var]    -- { data T x (y : Nat ) = B (T x) deriving (Z,W)}
  | Explicit ExplicitGADT
  | Kind Loc Var [Var] [(Var,[PT])]
  | Flag Var Var
  | Reject String [Dec]
  | Import String [Var]
  | TypeSyn Loc String Targs PT
  | TypeFun Loc String (Maybe PT) [([PT],PT)]

data Constr = Constr Loc Targs Var [PT] (Maybe [PPred])
type Strata = Int
data Program = Program [ Dec ]


monadDec location e = Val location pat (Normal e) []
  where pat = Pcon (Global "Monad")
                   [Pvar(Global "return") ,Pvar(Global "bind") ,Pvar(Global "fail")]


--------------------------------------------------
typeStrata = 0 :: Strata
kindStrata = 1 :: Strata
sortStrata = 2 :: Strata
classStrata = 3 :: Strata

strat 0 = "data"
strat 1 = "kind"
strat 2 = "sort"
strat 3 = "class"
strat n = "data@"++show n

---------------------------------------------------
isData (Data _ _ n _ _ _ _ _) | n == typeStrata = True
isData (Explicit (GADT loc n isProp nm knd cs)) | n == typeStrata = True
isData (TypeSig loc (Global (x:xs)) pt) | isUpper x = True
isData x = False

isKind (Data _ _ n _ _ _ _ _) | n == kindStrata = True
isKind (Explicit (GADT loc n isProp nm knd cs)) | n >= kindStrata = True
isKind (TypeSig loc (Global (x:xs)) pt) | isUpper x = True
isKind x = False

isTypeSig (TypeSig loc _ _) = True
isTypeSig _ = False

isTypeSyn (TypeSyn loc _ _ _) = True
isTypeSyn _ = False

isTypeFun (TypeFun _ _ _ _) = True
isTypeFun (TypeSig loc (Global (x:xs)) pt) = True
isTypeFun _ = False

-----------------------------------------------------------

instance Freshen Var => Freshen Pat where
  freshen (Plit x) = return(Plit x,[])
  freshen (Pvar v) = do { (v',ns) <- freshen v; return(Pvar v',ns)}
  freshen (Pprod p1 p2) =
     do {(p1',ns) <- freshen p1; (p2',ms) <- freshen p2; return (Pprod p1' p2',ms++ns)}
  freshen Pwild = return(Pwild,[])
  freshen (Psum i p) = do {(p',ns) <- freshen p; return (Psum i p',ns)}
  freshen (Pexists p) = do {(p',ns) <- freshen p; return (Pexists p',ns)}
  freshen (Paspat v p) =
     do { (v',ns) <- freshen v; (p',ms) <- freshen p; return(Paspat v' p',ms ++ ns)}
  freshen (Pcon c ps) =
     do { let acc2 p (ps,ns) = do { (p',ms) <- freshen p; return(p':ps,ms++ns)}
        ; (ps',ns) <- foldrM acc2 ([],[]) ps
        ; return(Pcon c ps',ns)}
  freshen (Pann p t) = do {(p',ns) <- freshen p; return (Pann p' t,ns)}

----------------------------------------------------------
-- How to deal with N-tuples


patTuple :: [Pat] -> Pat     -- Form a Pat like (x,y:ys)
patTuple [] = Plit Unit      -- (x,y,z,w) --> (x,(y,(z,w)))
patTuple [p] = p
patTuple [x,y] = Pprod x y
patTuple (x:xs) = Pprod x (patTuple xs)

expTuple :: [Exp] -> Exp -- Form an Expression with is a tuple like (3,4-9)
expTuple [] = Lit Unit
expTuple [p] = p
expTuple [x,y] = Prod x y
expTuple (x:xs) = Prod x (expTuple xs)

-------------------------------------------------------------------
-- Defining Infix and Prefix operators

opList prefix op left right none =
    [ [ prefix "-", prefix "+", prefix "#-" ]
    , [ op "!!" left]
    , [ op "^"  right]
    , [ op "*"  left, op "/"  left, op "#*"  left, op "#/"  left]
    , [ op "+"  left, op "-"  left, op "#+"  left, op "#-"  left]
    , [ op ":" right]
    , [ op "++" right]
    , [ op "==" none, op "/=" none, op "<"  none
      , op "<=" none, op ">"  none, op ">=" none
      , op "#==" none, op "#/=" none, op "#<"  none
      , op "#<=" none, op "#>"  none, op "#>=" none]
    , [ op "&&" none ]
    , [ op "||" none ]
    , [ op "<|>" right , op "<!>" right ]
    , [ op "$" right ]
    , [ op "." left]
   ]

metaHaskellOps = filter (/="") (concat (opList prefix op 0 0 0))
  where prefix x = ""
        op x y = x

infixp s = elem s metaHaskellOps

------------ Helper Functions -----------------------------------

binop nm e1 e2 = App(App (Var (Global nm)) e1) e2

decname (Val loc pat b ds) = patBinds pat
decname (Fun loc nm _ cs) = [nm]
decname (Pat loc nm ps p) = [nm]
decname (Data loc b strata nm sig args cs ds) = nm : map f cs
  where f (Constr loc skol nm ts eqs) = nm
decname (Explicit (GADT loc n isProp nm knd cs)) = nm : map f cs
  where f (loc,c,free,preds,typ) = c
decname (TypeSyn loc nm args ty) = [Global nm]
decname (TypeFun loc nm k ms) = [Global nm]
decname (Kind loc nm args ts) = nm : map f ts
  where f (nm,ts) = nm
decname (TypeSig loc nm t) = [proto nm]
decname (Prim loc nm t) = [nm]
decname (Flag s nm) =[flagNm nm]
decname (Reject s ds) = concat (map decname ds)
decname (Import s xs) = []
-- decname (Monad loc e) = [Global "monad"]

decloc :: Dec -> [(Var,Loc)]
decloc (Val loc pat b ds) = map (\ nm -> (nm,loc)) (patBinds pat)
decloc (Fun loc nm _ cs) = [(nm,loc)]
decloc (Pat loc nm ps p) = [(nm,loc)]
decloc (Data loc b strata nm sig args cs ds) = [(nm,loc)] ++ map f cs
  where f (Constr loc skol nm ts eqs) = (nm,loc)
decloc (Explicit (GADT loc n isProp nm knd cs)) = [(nm,loc)] ++ map f cs
  where f (loc,c,free,preds,typ) = (c,loc)
decloc (TypeSyn loc nm args ty) = [(Global nm,loc)]
decloc (TypeFun loc nm ty ms) = [(Global nm,loc)]
decloc (Kind loc nm args cs) = [(nm,loc)] ++ map f cs
  where f (nm,ts) = (nm,loc)
decloc (TypeSig loc nm t) = [(proto nm,loc)]
decloc (Prim loc nm t) = [(nm,loc)]
decloc (Flag s nm) =[]
decloc (Reject s d) = decloc (head d)
decloc (Import s vs) = []
-- decloc (Monad loc e) = [(Global "monad",loc)]

patf :: (Var -> Var) -> Pat -> Pat
patf f p =
 case p of
   Plit c -> Plit c
   Pvar n -> Pvar(f n)
   Pprod x y -> Pprod (patf f x) (patf f y)
   Psum inj y -> Psum inj (patf f y)
   Pexists x -> Pexists (patf f x)
   Paspat n p -> Paspat (f n) (patf f p)
   Pwild -> Pwild
   Pcon n ps -> Pcon n (map (patf f) ps)
   Pann p t -> Pann (patf f p) t

patg :: (Pat -> Pat) -> Pat -> Pat
patg f p =
 case p of
   Plit c -> Plit c
   Pvar n -> Pvar n
   Pprod x y -> Pprod (f x) (f y)
   Psum inj y -> Psum inj (f y)
   Pexists y -> Pexists (f y)
   Paspat n p -> Paspat n (f p)
   Pwild -> Pwild
   Pcon n ps -> Pcon n (map f ps)
   Pann p t -> Pann (f p) t



walkPat :: Monad m => (Var -> m b) -> [b] -> Pat -> m [b]
walkPat f ans p =
 case p of
   Plit c -> return ans
   Pvar n -> do { x <- f n; return(x : ans) }
   Pprod x y -> do { a <- walkPat f ans x; b <- walkPat f ans y; return (a++b) }
   Psum inj x -> walkPat f ans x
   Pexists x -> walkPat f ans x
   Paspat n p -> do { x <- f n; walkPat f (x :ans) p }
   Pwild -> return ans
   Pcon nm ps -> do { xss <- mapM (walkPat f ans) ps; return(concat xss) }
   Pann p t -> walkPat f ans p

patBinds p = concat(walkPat (:[]) [] p)

instance Eq Lit where
  (Int n) == (Int m) = n==m
  (Char n) == (Char m) = n==m
  (Symbol n) == (Symbol m) = n==m
  Unit == Unit = True
  (ChrSeq n) == (ChrSeq m) = n==m
  (Float n) == (Float m) = n==m
  (Tag s) == (Tag t) = s==t
  _ == _ = False


applyE :: [Exp] -> Exp
applyE [t] = t
applyE [x,y] = App x y
applyE (x : y : z) = applyE ((App x y):z)


pos x xs = p xs 0
  where p (y:ys) n = if x==y then Just n else p ys (n+1)
        p [] n = Nothing


-------------------------------------------------
-- Making Patterns and Expressions

truePat  = Pcon (Global "True") []
falsePat = Pcon (Global "False") []


ifExp (l1,l2) x y z = Case x [(l1,truePat,Normal y,[]),(l2,falsePat,Normal z,[])]

consExp x y = App (App (Var (Global ":")) x) y
nilExp = (Var (Global "[]"))

listExp = foldr consExp nilExp

unitExp = Lit Unit


------------ Binding Groups -----------------

ungroup d = [d]

group [d] = d

-- To collect separate clauses into one function
-- Also deal with collecting things into binding groups
-- we build a little finite state machine

mf [] = []
mf [x] = [x]
mf ((x1 @ (Fun l1 n1 h1 c1)) : (x2 @ (Fun l2 n2 h2 c2)) : xs) =
   if n1==n2 then mf ((Fun l1 n1 (mergeM h1 h2) (c1++c2)):xs)
             else x1 : (mf (x2:xs))
mf (x:xs) = x : mf xs

mergeM (Just x) _ = Just x
mergeM Nothing y = y

mergeFun ds = state0 ds -- return(mf ds) --

data DT = Fn Var | V | D | S | P | Syn | PT | TS Var | Flg | Rej | Pr | Im | TFun String
dt (Fun _ x _ _) = Fn x
dt (Val _ _ _ _) = V
dt (TypeSig loc n _) = TS n
dt (Prim loc n _) = Pr
dt (Data _ _ _ _ _ _ _ _) = D
dt (Explicit _) = D
dt (Kind _ _ _ _) = D
dt (TypeSyn _ _ _ _) = Syn
dt (TypeFun _ s _ _) = TFun s
dt (Pat _ _ _ _) = PT
dt (Flag _ _) = Flg
dt (Reject s d) = Rej
dt (Import s vs) = Im


state0 :: Monad m => [Dec] -> m[Dec]
state0 [] = return []
state0 (d:ds) = case dt d of
  Fn x -> state1 x [d] [] ds    -- state1 is collecting contiguous clauses with same function name
  V   -> do { xs <- state0 ds; return(d:xs) }    -- x = [1,2,3]
  Flg   -> do { xs <- state0 ds; return(d:xs) }  -- flag noisy
  PT  -> do { xs <- state0 ds; return(d:xs) }    -- C a y = (x:y:[])  -- a pattern declaration
  TS n -> do { xs <- state0 ds; return(d:xs) }   -- id :: a -> a -- a type signature
  Pr -> do { xs <- state0 ds; return(d:xs) }     -- prim f :: t
  D   -> do { xs <- (state0 ds); return (d:xs)}  -- data T x = C x | D Int
  Rej -> do { xs <- state0 ds; return(d:xs) }    -- ##test "test 3" x = 5
  Im -> do { xs <- state0 ds; return(d:xs) }
  Syn -> do { xs <- state0 ds; return(d:xs) }
  TFun s ->  state2 s [d] [] ds -- state2 is collecting contiguous clauses with same Type function name
  other -> fail ("Unknown Dec in state0: "++(show d))


state2 nm cls grps [] = final2 cls grps []
state2 nm cls grps (d:ds) = case dt d of
  TFun x -> if nm==x
               then state2 x (d:cls) grps ds
               else do { xs <- (state0 (d:ds)); final2 cls grps xs}
  other -> do { xs <- state0 (d:ds); final2 cls grps xs }

final2 cls grps ds = return((group (reverse ((merge2 (reverse cls)):grps))) : ds)

merge2 [] = error "shouldn't happen"
merge2 [d] = d
merge2 ((TypeFun l1 n1 k1 c1):(TypeFun l2 n2 k2 c2):ds) =
   if n1==n2
      then merge2 ((TypeFun l1 n1 (mergeM k1 k2) (c1++c2)):ds)
      else error "different names in merge"



state1 nm cls grps [] = final cls grps []
state1 nm cls grps (d:ds) = case dt d of
  Fn x -> if nm==x
            then state1 x (d:cls) grps ds
            else do { xs <- (state0 (d:ds)); final cls grps xs}
  other -> do { xs <- state0 (d:ds); final cls grps xs }

final cls grps ds = return((group (reverse ((merge (reverse cls)):grps))) : ds)

merge [] = error "shouldn't happen"
merge [d] = d
merge ((Fun l1 n1 h1 c1):(Fun l2 n2 h2 c2):ds) =
   if n1==n2
      then merge ((Fun l1 n1 (mergeM h1 h2) (c1++c2)):ds)
      else error "different names in merge"

--------------- Show Instances ---------------------


instance Show Lit where
  show (Int n) = show n
  show (Char c) = show c
  show (Symbol s) = "'"++show s
  show Unit = "()"
  show (ChrSeq s) = "#"++show s
  show (Float n) = show n
  show (Tag s) = "`"++ s
--  show (Scheme s) = "<Scheme>"


instance Show Pat where
  show (Plit c) = show c
  show (Pvar s) = show s
  show (Pprod x y) = "("++show x ++","++show y++")"
  show (Psum L x) = "(L "++(show x)++")"
  show (Psum R x) = "(R "++(show x)++")"
  show (Pexists x) = "(Ex "++(show x)++")"
  show (Paspat x p) = "("++ show x ++ " @ " ++ show p ++ ")"
  show Pwild = "_"
  show (Pcon x []) = show x
  show (Pcon x ps) = "("++ show x ++ (plist " " ps " " ")")
  show (Pann p t) = "("++show p++" :: "++show t++")"


parExp (x @ (Var _)) = show x
parExp (x @ (Lit _)) = show x
parExp (x @ (Prod _ _)) = show x
parExp (x @ (Escape _)) = show x
parExp (x @ (Reify s _)) = show x
parExp x = case isList x of
             Just z -> prList z
             Nothing -> "(" ++ show x ++")"

parFun (x @ (App _ _)) = show x
parFun x = parExp x

-----------------------------------------------
-- Showing lists using syntactic shorthand

isList (App (App (Var (Global ":")) x) y) =
       do { ys <- isList y; return (x:ys)}
isList (Var (Global "[]")) = Just []
isList _ = Nothing

x2 = listExp (map (Lit . Char) "asd")

isChar (Lit (Char _)) = True
isChar _ = False
charOf (Lit (Char c)) = c

prList xs | all isChar xs = show(map charOf xs)
prList xs = show xs

doList x = fmap prList (isList x)

--------------------------------------------------------
-- showing an operator in infix notation

isOp (App (App (Var (Global f)) x) y) = if infixp f then Just (x,f,y) else Nothing
isOp (App (App (Reify s v) x) y) = if infixp s then Just (x,s,y) else Nothing
isOp _ = Nothing


---------------------------------------------------------
-- Showing a thing with multiple ways to show it

data Fpair x y = forall t . Fpair (x -> Maybe t) (t -> y)

tryL :: a -> [Fpair a b] -> Maybe b
tryL x [] = Nothing
tryL x ((Fpair f g):fs) =
   case f x of
      Just x -> Just(g x)
      Nothing -> tryL x fs

-----------------------------------------------

instance Show Exp where
  show (Var s) = show s
  show (Lit c) = show c
  show (x @ (App a b)) =
    case (tryL x [Fpair isList prList,Fpair isOp doOp]) of
      Just ans -> ans
      Nothing -> (parFun a)++" "++(parExp b)
    where doOp (a,b,c) = (parFun a)++" "++b++" "++(parFun c)
  show (Lam ps e xs) = "\\ "++(plist "" ps " " "")++" -> "++(show e)
  --show (Lam [p] e) = "\\ "++(show p)++" -> "++(show e)
  show (Prod x y) = "("++show x++","++show y++")"
  show (CheckT x) = "(Check "++show x++")"
  show (Lazy x) = "(Lazy "++show x++")"
  show (Exists x) = "(Ex "++show x++")"
  show (Under p x) = "(under "++show p++" "++show x++")"
  show (Sum L x) = "(L "++show x++")"
  show (Sum R x) = "(R "++show x++")"
  show (Bracket e) = "[| " ++ (show e) ++ " |]"
  show (Escape  (Var s)) = "$"++ show s
  show (Escape e) = "$("++show e++")"
  show (Run e) = "run (" ++ show e++")"
  show (Reify s (Vlit c)) = show c
  show (Reify s v) = "%"++s
  show (Ann x t) = "("++show x++"::"++ show t ++ ")"

  show (Let ds e) = "let "++(plistf gg "{" ds "; " "}")++" in "++(show e)
     where gg d = show d ++ "\n"
  show (Circ vs e ds) = "circuit "++f vs++(show e)++
                     (plistf show " where\n  " ds "\n  " "\n")
      where f [] = ""
            f xs = plist "(" xs "," ") "
  show (Case e xs) = "case "++(show e)++" of "++(plistf sMatch "{" xs "; " "}")
  show (Do stmts) = "do "++(plist "{ " stmts "; " "}")


showListExp xs =
    if all litchar xs then show(map getchar xs) else plist "[" xs "," "]"
 where litchar (Lit (Char c)) = True
       litchar _ = False
       getchar (Lit (Char c)) = c


instance Show e => Show (Body e) where
  show Unreachable = "unreachable"
  show (Normal e) = show e
  show (Guarded xs) = plistf  f "| " xs " | " ""
    where f (x,y) = show x ++ " = " ++ show y

sMatch (loc,p,body,ds) = (show p)++" -> "++(show body)++sWhere ds
sWhere [] = ""
sWhere ds = " where "++(plist "{" ds "; " "}")

sClause nm (loc,ps,b,ds) = show nm++" "++(plist "" ps " " " = ")++(show b)++(sWhere ds)


instance (Show p, Show e,Show d) => Show (Stmt p e d) where
  show (BindSt loc p e) = (show p)++" <- "++(show e)
  show (LetSt loc ds) = "let "++(plistf gg "" ds "\n   " "")
          where gg d = "\n   "++show d
  show (NoBindSt loc e) = (show e)

instance Show Dec where
  show (Fun loc name Nothing cls) = plistf (sClause name) "\n" cls "\n" "\n"
  show (Fun loc name (Just hint) cls) =
      "\n*"++show name++" :: "++show hint++
      (plistf (sClause name) "\n" cls "\n" "\n")
  show (Val loc p b ds) = (show p)++" = "++(show b)++(sWhere ds)
  show (Pat loc nm ps p) = show nm ++ (plist " " ps " " " = ")++(show p)++"\n"
  show (TypeSig loc name typ) = show name++" :: "++ (show typ) ++ "\n"
  show (Prim loc name typ) = "prim "++show name++" :: "++ (show typ) ++ "\n"
  show (Data loc b n nm sig args cs ders) = showSig sig ++
     (strat n)++" "++show nm++(plistf showArg " " args " " "")++(plistf sConstr "\n = " cs "\n | " "")
    where showArg (x,AnyTyp _) = show x
          showArg (x,t) = "("++show x++"::"++show t++")"
          showSig Nothing = ""
          showSig (Just pt) = show nm ++" :: "++show pt++"\n"
  show (Explicit d) = show d
  show (Kind loc nm args cs) =
     "kind "++show nm++(plistf show " " args " " "")++(plistf f "\n = " cs "\n | " "")
   where f (nm,ts) = show nm ++ plistf showp " " ts " " ""
  show (Flag s nm) = "flag "++ show s++" "++ show nm
  show (Reject s ds) = "\n##test "++show s++"\n"++(plist "{" ds "; " "}")
  show (Import s vs) = "\nimport "++s ++plist "(" vs "," ")"++ "\n"
  -- show (Monad loc e) = "monad "++show e
  show (TypeSyn loc nm args ty) = "type "++nm++(plist "" args " " "")++" = "++show ty
  show (TypeFun loc nm k ms) = nm++showK k++"\n"++matches
    where matches = plistf g "" ms "\n" ""
          g (xs,e) = plist "{" xs " " "}"++" = "++show e

showK Nothing = " "
showK (Just k) = " :: "++show k

sConstr (Constr loc ex c ts eqs) = (exists ex)++show c++(args ts)++eqf eqs
  where args [] = ""
        args ts = " "++(plistf parenT "" ts " " "")
        exists [] = ""
        exists ns = "forall "++(plistf showM "" ns " " " . ")
        parenT (x @ (TyApp' y _)) = g (root' y) x
          where g (TyCon' "(,)")    y = show y
                g (TyCon' "(+)") y = show y
                g x y = "("++(show y)++")"
        parenT x = show x
        eqf (Just xs) = " where "++ plistf show "" xs ", " ""
        eqf Nothing = ""
        --g (x,y) = show x ++ " = " ++ show y
        showM (x,AnyTyp _) = show x
        showM (x,k) = "("++show x++"::"++show k++")"


root' (TyApp' x y) = root' x
root' x = x


instance Show Program where
  show (Program ds) = plist "\n" ds "\n" ""


instance Functor Body where
  fmap f Unreachable = Unreachable
  fmap f (Normal e) = Normal (f e)
  fmap f (Guarded ps) = Guarded(map (\ (x,y) -> (f x, f y)) ps)


--------------------------------------------------------------------------
-- The binding structure of Exp's is complicated by embedded [Dec]. We need
-- a function that given some "direction" on 1) how to process binding
-- ocurrences and 2) handle other occurences, then walks over an Exp and
-- repects this complicated structure rebuilding the term under this
-- "direction". We also want to handle the counting of levels implicit in
-- (Bracket e) and (Escape e). We embed this direction in the (Par m)
-- data structure.

data Par m =
   Par { varExt :: Var -> m(Var,Par m)  -- How to handle a binding Var
       , varApp :: Var -> m Exp   -- How to handle an "other" Var
       , incP :: Par m            -- How (Par m) changes when under Bracket.
       , escFun :: Exp -> m Exp } -- What to do when walking under Escape.

parThread alpha f [] = return ([],f)
parThread alpha f (s:ss) =
  do { (s2,f2) <- alpha s f
     ; (ss2,f3) <- parThread alpha f2 ss
     ; return(s2:ss2,f3)}

-- Walk over a Pat building extended (Par m)
parPat :: Monad m => Pat -> Par m -> m(Pat,Par m)
parPat (Plit x) f = return(Plit x,f)
parPat (Pvar v) f = do { (v',g) <- varExt f v; return(Pvar v',g)}
parPat (Pprod p1 p2) f =
  do {(p1',f1) <- parPat p1 f
     ; (p2',f2) <- parPat p2 f1
     ; return (Pprod p1' p2',f2)}
parPat (Pwild) f = return(Pwild,f)
parPat (Psum i p) f = do {(p',f1) <- parPat p f; return (Psum i p',f1)}
parPat (Pexists p) f = do {(p',f1) <- parPat p f; return (Pexists p',f1)}
parPat (Paspat v p) f =
  do { (v',f1) <- varExt f v
     ; (p',f2) <- parPat p f1
     ; return(Paspat v' p',f2)}
parPat (Pcon c ps) f =
  do { (ps',f2) <- parThread parPat f ps; return(Pcon c ps',f2)}
parPat (Pann p t) f = do {(p',f1) <- parPat p f; return (Pann p' t,f1)}

-- Walk over Exp, processing according to (Par m)
parE :: Monad m => Exp -> Par m -> m Exp
parE (Var s) f = varApp f s
parE (Lam ps e free) f =
   do { (ps',f1) <- parThread parPat f ps
      ; e' <- parE e f1
      ; return(Lam ps' e' free)}
parE (Lit c) f = return(Lit c)
parE (Sum inj x) f = do { a <- parE x f; return(Sum inj a) }
parE (Prod x y) f = do { a <- parE x f; b <- parE y f; return(Prod a b) }
parE (CheckT x) f = do { a <- parE x f; return(CheckT a)}
parE (Lazy x) f = do { a <- parE x f; return(Lazy a)}
parE (Exists x) f = do { a <- parE x f; return(Exists a)}
parE (Under x y) f = do { a <- parE x f; b <- parE y f; return(Under a b) }
parE (App x y) f = do { a <- parE x f; b <- parE y f; return(App a b) }
parE (Bracket x) f = do { a <- parE x (incP f); return (Bracket a) }
parE (Escape x) f = escFun f x
parE (Run x) f = do {a <- parE x f; return (Run a) }
parE (Reify s v) f = return(Reify s v)
parE (Case e ms) f =
   do { e2 <- parE e f
      ; ms2 <- mapM (\ m -> parMatch m f) ms
      ; return(Case e2 ms2)}
parE (Let ds e) f =
   do { (ds2,f2) <- extDs ds f
      ; ds3 <- parDs ds2 f2
      ; e3 <- parE e f2
      ; case e3 of
          Let ds4 e4 -> return(Let (ds3++ds4) e4)
          _ -> return(Let ds3 e3)
      }
parE (Circ vs e ds) f =
   do { (ds2,f2) <- extDs ds f
      ; vs2 <- mapM (varApp f) vs
      ; let unVar (Var s) = s
      ; ds3 <- parDs ds2 f2
      ; e3 <- parE e f2
      ; return(Circ (map unVar vs2) e3 ds3)
      }
parE (Do ss) f = do { (ss2,_) <- parThread parStmt f ss; return(Do ss2) }
parE (Ann x t) f = do { a <- parE x f; return(Ann a t)}

-- extDs just processes the binding ocurrences in the list of Dec, and leaves
-- the other sub-terms alone. It also computes a new parameter data-structure.
-- See parDs for the function that processes these subterms. This is necessary
-- since we get lists of mutually recursive Dec's, so we need to process every
-- binding ocurrence first, get one big extended parameter data structure, and
-- then apply it to all subterms

extDs ::  Monad m => [Dec] -> Par m -> m([Dec],Par m)
extDs ds f = parThread extD f ds

extD :: Monad m => Dec -> Par m -> m(Dec,Par m)
extD (Fun l nm hint cs) f = do { (nm2,f2) <- varExt f nm; return(Fun l nm2 hint cs,f2) }
extD (Val l p b ds) f = do { (p2,f2) <- parPat p f; return(Val l p2 b ds,f2) }
extD d f = return(d,f)

parDs :: Monad m => [Dec] -> Par m -> m [Dec]
parDs ds f = mapM (\ d -> parD d f) ds

parD :: Monad m => Dec -> Par m -> m Dec
parD (Fun a nm hint cs) f =
   do { cs2 <- mapM (parClause f) cs; return(Fun a nm hint cs2)}
parD (Val l p b ds) f =
   do { (ds1,f2) <- extDs ds f
      ; ds2 <- parDs ds1 f2
      ; b2 <- parBody b f2
      ; return(Val l p b2 ds2)}
--parD (Monad loc e) f = do { e2 <- parE e f; return(Monad loc e2) }
parD d f = return d

parClause::Monad m => Par m -> Match [Pat] Exp Dec -> m (Match [Pat] Exp Dec)
parClause f (loc,ps,body,ds) =
   do { (ps2,f2) <- parThread parPat f ps
      ; (ds2,f3) <- extDs ds f2
      ; ds3 <- parDs ds2 f3
      ; b2 <- parBody body f3
      ; return(loc,ps2,b2,ds3)}

parMatch :: Monad m => Match Pat Exp Dec -> Par m -> m (Match Pat Exp Dec)
parMatch (loc,p,body,ds) f =
   do { (p2,f2) <- parPat p f
      ; (ds2,f3) <- extDs ds f2
      ; ds3 <- parDs ds2 f3
      ; b2 <- parBody body f3
      ; return(loc,p2,b2,ds3)}

parBody :: Monad m => Body Exp -> Par m -> m(Body Exp)
parBody Unreachable f = return Unreachable
parBody (Normal e) f = do { e2 <- parE e f; return(Normal e2) }
parBody (Guarded xs) f = do { ys <- mapM g xs; return(Guarded xs) }
  where g (e1,e2) = do {e3 <- parE e1 f; e4 <- parE e2 f; return(e3,e4) }

parStmt :: Monad m => Stmt Pat Exp Dec -> Par m -> m(Stmt Pat Exp Dec,Par m)
parStmt (BindSt loc p e) f =
   do { e2 <- parE e f; (p2,f2) <- parPat p f; return(BindSt loc p2 e2,f2)}
parStmt (LetSt loc ds) f =
   do {(ds2,f2) <- extDs ds f; ds3 <- parDs ds2 f2; return(LetSt loc ds3,f2)}
parStmt (NoBindSt loc e) f = do { e2 <- parE e f; return(NoBindSt loc e2,f)}


----------------------------------------------------------------------------
-- After Parsing, an Exp is filled with (Global s) Var's. We need to walk
-- over the parse tree and replace them with fresh (Alpha s name) vars.
-- Hidden inside the Par data structure is some state which is a function:
-- Var -> m Exp. As we process binding occurences, this function is extended.

freshE :: (Fresh m,HasNext m) => Exp -> m Exp
freshE e = parE e (makeRenamer Var)

makeRenamer f = Par ext app inc esc
   where ext var = do { (var',f') <- genV var f; return(var',makeRenamer f') }
         app var = return(f var)
         inc = Par ext app inc esc
         esc e = do { x <- parE e (Par ext app inc esc); return(Escape x)}

-- Generate a new name, and extend the renaming function for a Var.

genV v f =
    do { n <- fresh; let new = Alpha (name v) n
       ; return(new,ext f v (Var new)) }
  where name (Global s) = s
        name (Alpha s n) = s
        ext f s ans t = if s==t then ans else f t

----------------------------------------------------------
-- A practice example that uses the level counting feature

swp e = parE e (makeSwapper 0 [])

makeSwapper level perm = Par ext app inc esc
  where ext (Global s) = return(Global s,makeSwapper level perm)
        ext (Alpha s n) = do { n' <- fresh; return(Alpha s n',makeSwapper level((n,n'):perm)) }
        app v = return(Var (swaps perm v))
        inc = makeSwapper (level+1) perm
        esc e = case level of
                 0 -> fail "Escape at level 0"
                 1 -> fail "eval embedded escape"
                 2 -> parE e (makeSwapper (level - 1) perm)


--subExp :: [(Var,Exp)] -> Exp -> a Exp
subExp xs e = parE e (makeSubst xs)

makeSubst xs = Par ext app inc esc
  where ext v = return(v,makeSubst ((v,Var v):xs))
        app v = case lookup v xs of
                  Just e -> return e
                  Nothing -> return(Var v)
        inc = Par ext app inc esc
        esc e = parE e (makeSubst xs)

------------------------------------------------------------
-- =========================================================


----------------------------------------------------------------
-- Computing 1) variables bound, 2) Variables that are depended on (but don't
-- necessarily appear free, i.e. constructors mentioned in Patterns, and
-- prototype declarations), 3) free variables in the value name space,
-- 4) variables bound in the type name space, and 5) free variables in
-- the type name space. For example:
--
-- length [] = 0
-- length (x:xs) = 1 + length xs
--
-- 1) binds      {length}
-- 2) depends on {:,[],::length}
-- 3) has free   {(+)}
--
-- To understand the ::length dependency, consider the related declaration:
-- length :: [a] -> Int
--
-- 1) binds                            {::length}
-- 2) depends on                       {length}
-- 3) has free                         {}
-- 4) binds in type name space         {a}
-- 5) has free vars in type name space {Int}
--
-- The circular dependency between "::length" and "length" cause both
-- declarations to be in the same mutually recursive binding block.

data FX = FX { binds   :: [Var]  -- Binds these variables (in value space)
             , depends :: [Var]  -- Depends on the Dec that binds these
                                 -- but they don't appear as free variables
             , free    :: [Var]  -- These occur free (implies dependancy)
             , tbinds  :: [Var]  -- Binds these (in type space)
             , tfree   :: [Var]  -- these type vars occur free (implies dependancy)
             }

instance Show FX where
  show (FX bs cs fs tbs tfs) =
    "\nBinds: "++show bs++
    "\nDepends On: "++show cs++
    "\nHas Free: "++show fs++
    "\nType Binds: "++show tbs++
    "\nType Free: "++show tfs++"\n"

-----------------------------
-- operations on the FX data structure

emptyF = FX [] [] [] [] []
appF (FX x y z m n) (FX a b c d e) =
   FX (union x a) (union y b) (union z c) (union m d) (union n e)

addFree bound v x = if mem v bound || mem v fs then x else x{free = v : fs}
  where fs = free x
        mem x xs = any (==x) xs
addBind v x = x {binds = v : binds x}
addDepend v x = x {depends = v : depends x}
addBindT ts x = x {tbinds = union ts (tbinds x)}
addFreeT ts x = x {tfree = union ts (tfree x)}

doBinders env = foldr f env ["return","bind","fail"]
  where f x env = addFree [] (Global x) env

underBinder :: Vars a => a -> ([Var] -> FX -> FX) -> [Var] -> FX -> FX
underBinder binders bindee bnd x = bindee (bnd2++bnd) (appF y2 x)
  where y = vars bnd binders emptyF  -- get the data structure
        bnd2 = binds y               -- extract names bound
        y2 = y {binds =[]}           -- erase them from the structure

underT s f x = FX a b c d (nub e \\ [y])
  where (FX a b c d e) = f x
        y = Global s

underTs ss f x = FX a b c d (nub e \\ ss)
  where (FX a b c d e) = f x

--------------------------------
-- Helper functions

typVar (Global (c:cs)) = isLower c
typVar _ = False

proto (Global s) = (Global ("::"++s))
proto x = x

showV :: Dec -> String
showV ds = show(vars [] [ds] emptyF)

---------------------------------
-- class definitions

class Vars t where
  vars :: [Var] -> t -> FX -> FX

class Binds t where
  boundBy :: t -> FX

varsL :: Vars a => [Var] -> [a] -> FX -> FX
varsL bnd [] = id
varsL bnd (p:ps) = vars bnd p . (varsL bnd ps)

varsLf f bnd [] = id
varsLf f bnd (p:ps) = f bnd p . (varsLf f bnd ps)


-----------------------------
-- Simple binds instances

instance Binds Pat where
  boundBy p = vars [] p emptyF

instance Binds Var where
  boundBy nm = addBind nm emptyF

---------------------------------------------------------------------
-- We process [Dec] in two steps, first compute those things bound
-- by using boundBy. Then, because a [Dec] is a mutually recursive binding
-- group, these names (in the value space) are passed to the second step
-- which computes the free variables (in both the value and type space)
-- Then ignoring the names bound in the second step, we combine the
-- things bound in the first step, with the things free in the second step.

-- Step 1. Compute just those things Bound by a Dec. This includes
-- the "binds", "depends" and "tbinds" fields

instance Binds Dec where
  boundBy (Val loc p body ds) = y {depends = map proto (binds y) ++ (depends y)}
     where y = boundBy p
  boundBy (Fun loc nm _ ms) = FX [nm] [proto nm] [] [] []
  boundBy (Pat loc nm nms p) = FX [nm] [] [] [] []
  boundBy (TypeSig loc v t) =
        if isTyCon v then FX [] [ ] [] (proto v :(nub binds)) [v]
                     else FX [proto v] [v] [] (nub binds) []
     where (FX _ _ _ tbs tfs) = vars [] t emptyF
           (binds,free) = partition typVar tfs
           isTyCon (Global (x:xs)) = isUpper x
           isTyCon _ = False
  boundBy (Prim l nm t) = FX [nm] [] [] [] constrs
     where (FX _ _ _ tbs tfs) = vars [] t emptyF
           (vs,constrs) = partition typVar tfs
  boundBy (Data l b 0 nm sig vs cs ders) = FX (map get cs) [] [] [nm] [proto nm]
     where get (Constr loc skol c ts eqs) = c
  boundBy (Explicit (GADT loc 0 isProp nm knd cs)) = FX (map get cs) [] [] [nm] [proto nm]
     where get (loc,c,free,preds,typ) = c

  boundBy (Data l b _ nm sig vs cs ders) = FX [] [] [] (nm : map get cs) [proto nm]
     where get (Constr loc skol c ts eqs) = c
  boundBy (Explicit (GADT loc 0 isProp nm knd cs)) = FX [] [] [] (nm : map get cs) [proto nm]
     where get (loc,c,free,preds,typ) = c

  boundBy (Kind l nm vs ts) = FX [] [] [] (nm: map get ts) []  -- everything here is in the Type name space
     where get (nm,ts) = nm
  boundBy (Import s vs) = FX [] [] [] [] []
  boundBy (TypeSyn loc nm args ty) = FX [] [] [] [Global nm] [proto (Global nm)]
  boundBy (TypeFun loc nm ty ms) = FX [Global nm] [proto (Global nm)] [] [] []
  boundBy _ = emptyF

dvars d = vars [] [d] emptyF

instance Binds d => Binds [d] where
  boundBy [] = emptyF
  boundBy (d:ds) = appF (boundBy d) (boundBy ds)

-- Step 2. Compute the fields other than those bound. Assume the
-- binding info is already in place. Includes "free" and "tfree" fields

instance Vars Dec where
  vars bnd (Val loc _ body ds) = underBinder ds (\ bnd -> vars bnd body) bnd
  vars bnd (Fun loc _ _ ms) = varsL bnd ms
  vars bnd (Pat loc nm nms p) = \ y -> foldr (addFree bnd) y (depends x)
     where x = vars [] p emptyF -- pattern C x y = (x,D y)  has "D" as free.
  vars bnd (Data loc b strata nm sig vs cs _) =
       underTs (map fst vs) (varsL bnd cs) . (varsL bnd (map snd vs)) . (vars bnd sig)

  vars bnd (Explicit (GADT loc 0 isProp nm knd cs)) =
       vars bnd knd . varsL bnd cs
  -- where get (loc,c,free,preds,typ) = c

  vars bnd (Kind loc _ vs ts) = underTs vs (varsL bnd ts)
  vars bnd (TypeSig loc v t) = addFreeT (nub free)
     where (FX _ _ _ tbs tfs) = vars bnd t emptyF
           (binds,free) = partition typVar tfs
  vars bnd (TypeSyn loc nm args ty) = underTs (map fst args) (vars bnd ty)
  vars bnd (TypeFun loc nm k ms) = varsL bnd ms
  vars bnd _ = id

instance Vars (Loc,Var,[([Char],PT)],[PPred],PT) where
  vars bnd (loc,c,free,preds,typ) =
    varsL bnd preds . vars bnd typ

instance Vars ([PT],PT) where
  vars bnd (args,body) = (addFreeT constrs) . (underTs vs (vars bnd body))
    where (FX _ _ _ _ argfree) = varsL bnd args emptyF
          (vs,constrs) = partition typVar argfree

instance Vars a => Vars (Maybe a) where
  vars bnd (Just x) = vars bnd x
  vars bnd Nothing = id


-- Organize and sequence the two steps
-- Combine "binds" "depends" "tbinds" from step 1
-- with "free" abd "tfree" of second step.

instance Vars [Dec] where
  vars bnd ds x = FX vbnd deps fs tbnd (tfs ++ tfs2)               -- Combine
    where (FX vbnd deps    _  tbnd tfs2 ) = boundBy ds             -- Step 1
          (FX _    _ fs _    tfs) = foldr (vars (vbnd++bnd)) x ds  -- Step 2

----------------------------------------------------
-- Vars instances for types other than [Dec]

instance Vars Constr where
  vars bnd (Constr loc skol nm args eqs) =
      underTs (map fst skol) (varsL bnd args . varsL bnd (map snd skol)) .
      underTs (map fst skol) (f eqs)

   where f Nothing = id
         f (Just xys) = varsL bnd xys


instance Vars (Var,[PT]) where
  vars bnd (_,ts) = varsL bnd ts

instance Vars PPred where
  vars bnd (Equality' x y) = vars bnd x . vars bnd y
  vars bnd (NotEqual' x y) = vars bnd x . vars bnd y
  vars bnd (Rel' nm ts) = addFreeT [Global nm] . vars bnd ts


instance Vars PT where
  vars bnd (TyVar' s) = addFreeT [Global s]
  vars bnd (TyCon' s) = addFreeT [Global s]
  vars bnd (TyApp' x y) = vars bnd x . vars bnd y
  vars bnd (Rarrow' x y) = vars bnd x . vars bnd y
  vars bnd (Karrow' x y) = vars bnd x . vars bnd y
  vars bnd (TyFun' (TyVar' f :xs)) = addFree bnd (Global f) .  varsL bnd xs
  --vars bnd (TyFun' (TyCon' f :xs)) = addFree bnd (Global f) . varsL bnd xs
  vars bnd (w@(TyFun' (f :xs))) = error ("Bad type function: "++show f++" -- "++show w)
  vars bnd (Star' _) = id
  vars bnd (Forallx q ss eqs t) = underTs args (vars bnd t) . underTs args (varsL bnd eqs)
    where args = (map (Global . fst3) ss)
          fst3 (a,b,c) = a
  vars bnd (Tlamx s t) = underTs [Global s] (vars bnd t)
  vars bnd (AnyTyp n) = id

instance Vars [(PT,PT)] where
  vars bnd [] = id
  vars bnd ((a,b):xs) = vars bnd a . vars bnd b . vars bnd xs

instance Vars Pat where  -- Modifies only the "binds" and "depends" fields
  vars bnd (Plit c) = id
  vars bnd (Pvar n) = addBind n
  vars bnd (Pprod x y) = (vars bnd y) . (vars bnd x)
  vars bnd (Psum inj x) = (vars bnd x)
  vars bnd (Pexists x) = (vars bnd x)
  vars bnd (Paspat n p) = (addBind n) . (vars bnd p)
  vars bnd (Pwild) = id
  vars bnd (Pcon nm ps) = addDepend nm . (varsL bnd ps)
  vars bnd (Pann p t) = vars bnd p

instance Vars Exp where
  vars bnd (Var v) = addFree bnd v
  vars bnd (Lit _) = id
  vars bnd (Sum _ e ) = vars bnd e
  vars bnd (Prod e1 e2) = (vars bnd e1) . (vars bnd e2)
  vars bnd (App e1 e2) = (vars bnd e1) . (vars bnd e2)
  vars bnd (Lam ps e xs) = underBinder ps (\ bnd -> vars bnd e) bnd
  vars bnd (Let ds e) = underBinder ds (\ bnd -> vars bnd e) bnd
  vars bnd (Circ vs e ds) = underBinder ds (\ bnd -> vars bnd e) bnd
  vars bnd (Case e ms)  = (vars bnd e) . (varsL bnd ms)
  vars bnd (Do ss) = vars bnd ss . doBinders
  vars bnd (CheckT x) = vars bnd x
  vars bnd (Lazy x) = vars bnd x
  vars bnd (Exists x) = vars bnd x
  vars bnd (Under e1 e2) = (vars bnd e1) . (vars bnd e2)
  vars bnd (Bracket e) = vars bnd e
  vars bnd (Escape e) = vars bnd e
  vars bnd (Run e) = vars bnd e
  vars bnd (Reify s v) = id
  vars bnd (Ann x t) = vars bnd x

evars e = vars [] e emptyF


instance (Vars p,Vars e,Vars [d]) => Vars (Match p e d) where
  vars bnd (loc,p,body,ds) =
      underBinder p (underBinder ds (\ b -> vars b body)) bnd

instance Vars [Pat] where  -- Necessary to make the (Vars (Match p e d)) instance
  vars = varsL      -- work when p is [p] (Fun matches as opposed to Case matches)

instance Vars e => Vars (Body e) where
  vars bnd Unreachable = id
  vars bnd (Normal e) = vars bnd e
  vars bnd (Guarded []) = id
  vars bnd (Guarded ((x,y):ps)) = vars bnd x . vars bnd y . vars bnd (Guarded ps)

instance Vars [Stmt Pat Exp Dec] where  -- Stmt's always come in lists, and their
  vars bnd [] = id                      -- scope extends down the list.
  vars bnd ((NoBindSt loc e):ss) = vars bnd e . vars bnd ss
  vars bnd ((LetSt loc ds):ss) = underBinder ds (\ bnd -> vars bnd ss) bnd
  vars bnd ((BindSt loc p e):ss) = underBinder p (\ bnd -> vars bnd ss . vars bnd e) bnd

------------------------------------------------------------------------
-- To compute topological sort we need a function that computes
-- names bound and names depended on for each Dec. Since we have
-- two distict name spaces. We "flag" names in the type name space
-- so they'll be distinct.

freeOfDec :: Dec -> ([Var],[Var])
freeOfDec d = (bound,deps)
  where x = vars [] [d] emptyF
        bound = binds x ++ map flagNm (filter (not . typVar) (tbinds x))
        deps = free x ++ depends x ++ map flagNm (tfree x)

flagNm (Global x) = Global("%"++x)
flagNm (Alpha x nm) = Alpha ("%"++x) nm

flagged (Global ('%':s)) = True
flagged (Alpha ('%':s) n) = True
flagged _ = False

declBindsFree vars d = binds(boundBy d)

-- expFV bound (Var x) = if x `elem` bound then [] else [x]


-- ====================================================================
-- To translate an explicitly typed data like:
-- data Nat :: *0 ~> Nat -> *0 where
--   Nil :: Seq a Z
--   Cons :: a -> Seq a m -> Seq a (S m)
--
-- into an equality qualified data
-- data Seq a n =
--   Nil where n = Z
--   exists m . Cons a m where n = S m
--
-- we use the function transGADT which proceeds in several steps
-- see the code and comments below.


data ExplicitGADT = GADT Loc Int Bool Var PT [(Loc,Var,[([Char],PT)],[PPred],PT)]

-- traceSh s x = unsafePerformIO(putStrLn ("\n--- Trace ---\n"++s++show x))

instance Show ExplicitGADT where
  show (GADT loc strata isProp nm knd cs) =
      ("data "++show nm++" :: "++show knd++" where \n"++
       plistf f "   " cs "\n   " "\n")
   where f (loc,c,free,preds,typ) = show c++" :: "++show typ

transGADT :: ExplicitGADT -> Dec
transGADT (GADT loc strata b (name@(Global t)) kind constrs) =
     Data loc b strata name (Just kind) (map f args) constrs' []
  where fresh = freshNames (map g constrs)
        (args,univ) = step1 fresh kind
        f (name,pt) = (Global name,pt)
        g (loc,constr,prefix,preds,typ) = typ
        forEachConstr (loc,c@(Global constr),prefix,preds,typ)
            = step4 (addToPrefix prefix prefix)
                    constr loc sub (map (ppredsub eqnsDup) preds2++equalities)
                    newrange domains (getFree [] newrange)
          where (domains,triples,newrange,eqnsDup) = step2 strata args (constr,typ)
                (sub,qual) = step3 triples
                g (t1,t2) = Equality' (ptsub sub t1) (ptsub sub t2)
                equalities = (map g (qual ++ map h eqnsDup))
                h (x,y) = (TyVar' x,TyVar' y)
                preds2 = map (ppredsub sub) preds
                -- if there prefix is not null then some one wrote
                -- Cons :: forall (a::k) . typ
                -- if "a" appears more than once then it gets renamed
                -- so we must add the renamed vars to prefix
                addToPrefix [] ans = ans
                addToPrefix ((name,pt):xs) ans =
                  case find (\ (dup,old) -> old==name) eqnsDup of
                    Nothing -> addToPrefix xs ans
                    Just(dup,old) -> addToPrefix xs (ans++[(dup,pt)])

        constrs' = map forEachConstr constrs


-- Generate an infinite list of names not occuring any place
-- in a PT, either free or bound
freshNames :: [PT] -> [String]
freshNames typs = makeNames "abcdefghijklmnopqrstuvwxyz" \\ used
   where used = foldr g [] typs
         g t free = union (getAll t) free

-- First Note that in an explicitly typed data the type of each constructor
-- is a Rho type. Because the parser has factored out any explicit forall.
-- getRange( T a -> [Int] -> T b ) ====> ([T a,[Int]],T b)
-- If the declaration is an explicit kind declaration, then it could be
-- a Karrow.

getRange 0 (Rarrow' d x) = (d:ds,r) where (ds,r) = getRange 0 x
getRange 1 (Karrow' d x) = (d:ds,r) where (ds,r) = getRange 1 x
getRange _ r = ([],r)

-- Step 1) Look at the kind (*0 ~> Nat -> *0) of the type being defined
-- (Seq) and then invent new fresh type variables and pair them up
-- with their kinds [(i,*0),(j,Nat)]

step1 n (Forallx _ ps _ t) = (pairs,map f ps ++ univ)
   where f (nm,k,q) = (nm,k)
         (pairs,univ) = step1 n t
step1 (n:ns) (Karrow' x y) = add (n,x) (step1 ns y)
   where add p (pairs,univ) = (p : pairs, univ)
step1 ns range = ([],[])

-- Step 2) For each constructor find its Range (which should be an
-- application of a type constructor like "T a b") Then replace each
-- argument (like a and b) with a corresponding fresh var (like i and j) to
-- get a NewRange, then triple up the actual arg with the cooresponding
-- fresh type variable and its kind. Compute equalities if any
-- var appears more than once in range
--
--   Constr  Domains      Range           Triples                  New Range      Eqns
--   Nil     []           Seq a Z         [(a,i,*0),(Z,j,Nat)]     Seq i j        []
--   Cons    [a,Seq a m]  Seq a (S m)     [(a,i,*0),(S m,j,Nat)]   Seq i j        []
--   In      [Exp c a t]  Decs c a a t    [(c,i,_),(a,j,_)         Decs i j k l   [(a=a1)]
--                                        ,(a1,k,_),(t,l,_)]

step2 :: Int -> [(String,PT)] -> (String,PT) -> ([PT],[(PT,PT,PT)],PT,[(String,String)])
step2 strata freshKindPairs (constr,typ) = (domains,triples,range3,eqns)
   where (domains,range) = getRange strata typ
         (range2,eqns) = duplicatesInRange (getAll typ) range
         (triples,range3) = tripleUp freshKindPairs range2

-- tripleUp [(i:k1),(j:k2)] (T a (S b)) -> ([(a,i,k1),(S b,j,k2)], T i j)
-- tripleUp :: [(String,pt)] -> PT -> ([(PT,PT,pt)],PT)
tripleUp [] (TyCon' t) = ([],TyCon' t)
tripleUp [] x =  ([],x)
tripleUp fresh_args (TyApp' x y) =
      ((y,TyVar' fname,knd):trips, TyApp' typ (TyVar' fname))
   where (fname,knd) = last fresh_args
         args = init fresh_args
         (trips,typ) = tripleUp args x
tripleUp args t = error ("\nBad "++show t++"\n"++show args++"\n")

-- Step 3) Split the triples into two parts, pairs of variables to
-- variables (a substitution), and pairs of variables to types
-- (an equality qualification).
--     Constructor   Triples                   Substitution     Qualification
--     Nil           [(a,i,*0),(Z,j,Nat)]      [(a,i)]          [(j,Z)]
--     Cons          [(a,i,*0),(S m,j,Nat)]    [(a,i)]          [(j,S m)]

step3 [] = ([],[])
step3 ((TyVar' x,TyVar' y,k):xs) = ((x,y):subs,quals)
   where (subs,quals) = step3 xs
step3 ((typ,TyVar' y,k):xs) = (subs,(TyVar' y,typ):quals)
   where (subs,quals) = step3 xs

-- Step 4) For each constructor, rebuild a new type, where the domains
-- are obtained by applying the subsitution to the old domains, and the
-- range is the new range obtained in step 1. Apply the substitution
-- to the qualification to get the qualification. Existentially
-- quantify all variables not appearing in the new range
--
--   Nil :: Seq i j  where j=Z
--   Cons :: exists m . i -> Seq i m -> Seq i j  where (j=S m)

step4 prefix c loc subs quals newrange domains rangeVars
       = Constr loc exists (Global c) doms eqls
   where doms = map (ptsub subs) domains
         constrType = foldr Rarrow' newrange doms
         allVars = union (getFree [] constrType) (getFreePredL [] quals)
         f t = (Global t, AnyTyp 1)
         g (t,x) = (Global t,x)
         exists = if null prefix
                    then (map f (allVars \\ rangeVars))
                    else map g prefix
         eqls = if null quals then Nothing else Just quals


-- Test if an explicit GADT is well formed
-- Nothing means yes, (Just errormessage) otherwise
okGADT :: ExplicitGADT -> Maybe String
okGADT (GADT loc strata b (Global tname) kind constrs) = okCONSTR constrs
  where okCONSTR [] = Nothing
        okCONSTR (quad:cs) = okAnd (test quad) (okCONSTR cs)
        okAnd Nothing xs = xs
        okAnd (Just s) xs = Just s
        test (cloc,Global cname,prefix,preds,ctype) = okRange cname cloc strata ctype
        okRange cname cloc 0 (Rarrow' x y) = okRange cname cloc 0 y
        okRange cname cloc 1 (Rarrow' x y) = Just ("To classify type Constructor: '"++cname++"' use (~>) not (->)")
        okRange cname cloc 1 (Karrow' x y) = okRange cname cloc 1 y
        okRange cname cloc 0 (Karrow' x y) = Just ("To classify value Constructor: '"++cname++"' use (->) not (~>)")
        okRange cname cloc n (Forallx _ _ _ z) = okRange cname cloc n z
        okRange cname cloc n typ = okAppOfT kind typ
          where okAppOfT (Karrow' x y) (TyApp' t z) = okAppOfT y t
                okAppOfT (Karrow' x y) t = Just
                         (show cloc ++
                          "\nRange of "++cname++" is not fully applied application of " ++
                          tname++"\n"++show t)
                okAppOfT (Forallx q ss eqs t) y = okAppOfT t y
                okAppOfT _ (f@(TyApp' _ _)) = Just
                         (show cloc ++
                          "\nkind: " ++
                          show kind ++
                          " is not consistent with range of "++cname++": "++
                          show typ)
                okAppOfT _ (TyCon' z) | z==tname = Nothing
                okAppOfT w t = Just
                         (show cloc ++
                          "\nrange of "++cname++" "++show t++
                          " is not consistent with type being defined "++
                          show tname++"\n "++show w)

gadt2Data (Explicit x) =
   case (okGADT x) of
        Nothing -> return(transGADT x)
        Just s -> fail s
gadt2Data x = return x

------------------------------------------------------------
-- if we have a constructor with a type where a variable
-- appears more than once in the range. E.g.
-- C:: (Exp c all t) -> Decs c all all t,  we need to rename
-- any variable that appears more than once, and collect a set
-- of equations.  [(all = all7)] => Decs c all all7 t

duplicatesInRange :: [[Char]] -> PT -> (PT,[(String,String)])
duplicatesInRange bad typ = (typ2,eqns)
  where (typ2,(_,mapping)) = rename (bad,[]) typ
        eqns = concat (map f mapping)
        f (x,[]) = []
        f (x,ys) = (map g ys) where g y = (y,x)

newname bad name = f 0
  where f n = let new = (name++show n)
              in if elem new bad then f (n+1) else new

rename :: ([String],[(String,[String])]) -> PT ->
          (PT,([String],[(String,[String])]))
rename (bad,mapping) (TyVar' s) = (TyVar' x,(badder,mapping2))
  where (x,badder,mapping2) = scan mapping
        scan [] = (s,s:bad,[(s,[])])
        scan ((x,xs):ms) | s==x = (y,y:bad,(x,y:xs):ms)
           where y = newname bad s
        scan (m:ms) = (y,badder,m:ms2)
           where (y,badder,ms2) = scan ms
rename used (Rarrow' x y) = (Rarrow' a b,u2)
  where (a,u1) = rename used x
        (b,u2) = rename u1 y
rename used (Karrow' x y) = (Karrow' a b,u2)
  where (a,u1) = rename used x
        (b,u2) = rename u1 y
rename used (TyFun' (x:xs)) =  (TyFun' (x:ys),u2)
  where (ys,u2) = renameL used xs
rename used (TyApp' x y) = (TyApp' a b,u2)
  where (a,u1) = rename used x
        (b,u2) = rename u1 y
rename used (TyCon' s) =  (TyCon' s,used)
rename used (Star' n) =  (Star' n,used)
rename used (AnyTyp n) =  (AnyTyp n,used)
rename used t = error ("The type: "++show t++" should not appear in the range of a GADT")

renameL u [] = ([],u)
renameL u1 (x:xs) = (y:ys,u3)
  where (y,u2) = rename u1 x
        (ys,u3) = renameL u2 xs


