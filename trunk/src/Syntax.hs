{-# LANGUAGE ExistentialQuantification
  , FlexibleInstances
  , FlexibleContexts
  , TypeSynonymInstances
  , UndecidableInstances
  #-}
module Syntax where

import Bind
import Monad
import Monads
import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import Auxillary
import List(elem,nub,union,(\\),partition,find)
import RankN(PT(..),showp,getAll,getFree,getFreePredL,applyT',ptsub,ppredsub
            ,getMult,PPred(..),Pred(..),Quant(..)
            ,definesValueConstr,short)

import SyntaxExt(Extension(..),extList,extKey,extM,ppExt,extThread,SynExt(..),synKey,synName)
import Char(isLower,isUpper,ord,chr)
import qualified Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.HughesPJ(Doc,text,int,(<>),(<+>),($$),($+$),render)

-- To import ParserAll you must define CommentDef.hs and TokenDef.hs
-- These should be in the same directory as this file.
import ParserAll(Parser)

-- By rights these should be defined in Value.hs but then
-- we'd have recursive import lists

data Ev = Ev [(Var,V)] -- Runtime environment mapping Vars to Values

showenv (Ev xs) =
  "Ev with \n   "++show (map fst xs)

type EnvFrag = [(Var,V)]

data V
  = Vlit Lit
  | Vsum Inj V
  | Vprod V V
  | Vprimfun String (V -> FIO V)
  | Vfun [Pat] Exp Ev
  | Vf (V -> FIO V) (Ev -> V) (Perm -> V)
  | Vcon (Var,SynExt String) [V]
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
  | CrossStage V

data Inj = L | R deriving (Eq,Show,Ord)

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
  | ExtP (Extension Pat)

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
  | Do (Exp,Exp) [Stmt Pat Exp Dec] -- { do { p <- e1; e2 } }
  | CheckT Exp
  | Lazy Exp
  | Exists Exp
  | Bracket Exp
  | Escape Exp
  | Reify String V
  | Ann Exp PT
  | ExtE (Extension Exp)

type Match p e d = (Loc,p,Body e,[d]) -- case e of { p -> b where decs }

data Body e
  = Guarded [(e,e)]           -- f p { | e1 = e2 | e3 = e4 } where ds
  | Normal e                  -- f p = { e } where ds
  | Unreachable

data Stmt p e d
  = BindSt Loc p e
  | LetSt Loc [d]
  | NoBindSt Loc e

data PrimBindings
  = Explicit Var PT                     -- { primitive bind :: a -> b }
  | Implicit [Var]                      -- { primitive import (a, b, c) }

data Dec
  = Fun Loc Var (Maybe PT) [Match [Pat] Exp Dec]   -- { f p1 p2 = b where decs }
  | Val Loc Pat (Body Exp) [Dec]        -- { p = b where decs }
  | Pat Loc Var [Var] Pat               -- { pattern Let x y z = App (Lam x z) y
  | TypeSig Loc [Var] PT                -- { id, di :: a -> a }
  | Prim Loc PrimBindings
  | Data Loc Bool Strata Var (Maybe PT) Targs [Constr] [Derivation] -- { data T x (y :: Nat) = B (T x) deriving (Z,W) }
  | GADT Loc Bool Var PT [(Loc,Var,[([Char],PT)],[PPred],PT)] [Derivation] (SynExt String)
  | Flag Var Var
  | Reject String [Dec]
  | AddTheorem Loc [(Var,Maybe Exp)]
  | Import String (Maybe [ImportItem])
  | TypeSyn Loc String Targs PT
  | TypeFun Loc String (Maybe PT) [([PT],PT)]


data Constr = Constr Loc Targs Var [PT] (Maybe [PPred])
type Strata = Int
data Program = Program [ Dec ]

data ImportItem
  = VarImport Var
   | SyntaxImport String String
 deriving Eq

monadDec location e = Val location pat (Normal e) []
  where pat = Pcon (Global "Monad")
                   [Pvar(Global "return"), Pvar(Global "bind"), Pvar(Global "fail")]

----------------------------------------------------

data Derivation = Syntax (SynExt String)

ppDeriv (Syntax Ox) = text ""
ppDeriv (Syntax z) = text (synName z++"("++synKey z++")")

instance Show Derivation where
  show x = render(ppDeriv x)

instance Eq Derivation where
 (Syntax x) == (Syntax y) = x==y

bindsDeriv (Syntax Ox) = id
bindsDeriv (Syntax x) = id -- addBind (Global ("#"++synName x++synKey x))

bindDs [] = id
bindDs (d:ds) = bindsDeriv d . bindDs ds

depExt x = addDepend(Global(extPrefix x ++ extKey x))

extPrefix :: Extension a -> String
extPrefix (Unitx s) = "#U"
extPrefix (Itemx x s) = "#I"
extPrefix (Listx xs _ s) = "#L"
extPrefix (Natx n x s) = "#N"
extPrefix (Pairx xs s) = "#P"
extPrefix (Recordx xs _ s) = "#R"
extPrefix (Tickx i _ s) = "#T"

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
isData (Data _ _ n _ _ _ _ _) = True
isData (GADT loc isProp nm knd cs ders ext) = True
isData (TypeSig loc [Global (x:xs)] pt) | isUpper x = True
isData _ = False

isTypeSig (TypeSig loc [_] _) = True
isTypeSig _ = False

isTypeSyn (TypeSyn loc _ _ _) = True
isTypeSyn _ = False

isTypeFun (TypeFun _ _ _ _) = True
isTypeFun (TypeSig loc [Global (x:xs)] (Karrow' _ _)) | isLower x = True
isTypeFun (TypeSig loc [Global (x:xs)] (Forallx _ _ _ (Karrow' _ _))) | isLower x = True
isTypeFun _ = False

isTheorem (AddTheorem _ _) = True
isTheorem _ = False
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
  freshen (ExtP xs) = do { xs' <- extM freshen xs
                         ; return(ExtP(fmap fst xs'),concat(extList(fmap snd xs')))}

----------------------------------------------------------
-- How to deal with N-tuples

patTuple :: [Pat] -> Pat     -- Form a Pat like (x,y:ys)
patTuple [] = Plit Unit      -- (x,y,z,w) --> (x,(y,(z,w)))
patTuple [p] = p
patTuple [x,y] = Pprod x y
patTuple (x:xs) = Pprod x (patTuple xs)

expTuple :: [Exp] -> Exp -- Form an Expression which is a tuple like (3,4-9)
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
decname (GADT loc isProp nm knd cs ders _) = nm : map f cs
  where f (loc,c,free,preds,typ) = c
decname (TypeSyn loc nm args ty) = [Global nm]
decname (AddTheorem dec xs) = []
decname (TypeFun loc nm k ms) = [Global nm]
decname (TypeSig loc [nm] t) = [proto nm]
decname (Prim loc (Explicit nm t)) = [nm]
decname (Flag s nm) =[flagNm nm]
decname (Reject s ds) = concat (map decname ds)
decname (Import s xs) = []

dnames (AddTheorem dec xs) = map fst xs
dnames d = decname d

decloc :: Dec -> [(Var,Loc)]
decloc (Val loc pat b ds) = map (\ nm -> (nm,loc)) (patBinds pat)
decloc (Fun loc nm _ cs) = [(nm,loc)]
decloc (Pat loc nm ps p) = [(nm,loc)]
decloc (Data loc b strata nm sig args cs ds) = [(nm,loc)] ++ map f cs
  where f (Constr loc skol nm ts eqs) = (nm,loc)
decloc (GADT loc isProp nm knd cs ders _) = [(nm,loc)] ++ map f cs
  where f (loc,c,free,preds,typ) = (c,loc)
decloc (TypeSyn loc nm args ty) = [(Global nm,loc)]
decloc (AddTheorem loc _) =[]
decloc (TypeFun loc nm ty ms) = [(Global nm,loc)]
decloc (TypeSig loc [nm] t) = [(proto nm,loc)]
decloc (Prim loc (Explicit nm t)) = [(nm,loc)]
decloc (Flag s nm) =[]
decloc (Reject s d) = decloc (head d)
decloc (Import s vs) = []

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
   ExtP x -> ExtP(fmap (patf f) x)

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
   ExtP x -> ExtP(fmap f x)

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
   ExtP p -> do { p' <- extM (walkPat f ans) p; return(concat(extList p'))}

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


compLit (Int n) (Int m) = Just(compare n m)
compLit (Char n) (Char m) = Just(compare n m)
compLit (Symbol n) (Symbol m) = Just(compare n m)
compLit Unit Unit = Just EQ
compLit (ChrSeq n) (ChrSeq m) = Just(compare n m)
compLit (Float n) (Float m) = Just(compare n m)
compLit (Tag n) (Tag m) = Just(compare n m)
compLit _ _ = Nothing


applyE :: [Exp] -> Exp
applyE [t] = t
applyE [x,y] = App x y
applyE (x : y : z) = applyE ((App x y):z)

unApply :: Exp -> [Exp] -> (Exp,[Exp])
unApply (App f x) args = unApply f (x:args)
unApply f args = (f,args)

pos x xs = p xs 0
  where p (y:ys) n = if x==y then Just n else p ys (n+1)
        p [] n = Nothing

-------------------------------------------------
-- Making Patterns and Expressions

truePat = Pcon (Global "True") []
falsePat = Pcon (Global "False") []

ifExp (l1,l2) x y z = Case x [(l1,truePat,Normal y,[]),(l2,falsePat,Normal z,[])]

consExp x y = App (App (Var (Global ":")) x) y
nilExp = (Var (Global "[]"))

listExp = foldr consExp nilExp
listExp2 xs nil = foldr consExp nil xs

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

data DT = Fn Var | V | D | S | P | Syn | PT | TS Var | Flg | Rej | Pr | Im | TFun String | Thm
dt (Fun _ x _ _) = Fn x
dt (Val _ _ _ _) = V
dt (TypeSig _ [n] _) = TS n
dt (Prim _ _) = Pr
dt (Data _ _ _ _ _ _ _ _) = D
dt (GADT _  _ _ _ _ _ _) = D
dt (TypeSyn _ _ _ _) = Syn
dt (TypeFun _ s _ _) = TFun s
dt (Pat _ _ _ _) = PT
dt (Flag _ _) = Flg
dt (Reject s d) = Rej
dt (Import s vs) = Im
dt (AddTheorem _ _) = Thm

expandTypeSigs loc pt = foldl (\ns n -> TypeSig loc [n] pt:ns)

state0 :: Monad m => [Dec] -> m[Dec]
state0 [] = return []
state0 (TypeSig loc ns pt:ds) | length ns > 1 = state0 (expandTypeSigs loc pt ds ns)
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
  Thm -> do { xs <- state0 ds; return(d:xs) }
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

instance Functor Body where
  fmap f Unreachable = Unreachable
  fmap f (Normal e) = Normal (f e)
  fmap f (Guarded ps) = Guarded(map (\ (x,y) -> (f x, f y)) ps)


--------------------------------------------------------------------------
-- The binding structure of Exp's is complicated by embedded [Dec]. We need
-- a function that given some "direction" on 1) how to process binding
-- occurrences and 2) handle other occurences, then walks over an Exp and
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
  do { (p1',f1) <- parPat p1 f
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
parPat (ExtP p) f = do { (p',f') <- extThread parPat f p; return(ExtP p',f')}

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
parE (App x y) f = do { a <- parE x f; b <- parE y f; return(App a b) }
parE (Bracket x) f = do { a <- parE x (incP f); return (Bracket a) }
parE (Escape x) f = escFun f x
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
parE (Do (bi,fa) ss) f = do { bind <- parE bi f
                            ; fail <- parE fa f
                            ; (ss',_) <- parThread parStmt f ss
                            ; return(Do (bind,fail) ss') }
parE (Ann x t) f = do { a <- parE x f; return(Ann a t)}
parE (ExtE y) f = do { z <- extM (\ x -> parE x f) y; return(ExtE y)}

-- extDs just processes the binding occurrences in the list of Dec, and leaves
-- the other sub-terms alone. It also computes a new parameter data-structure.
-- See parDs for the function that processes these subterms. This is necessary
-- since we get lists of mutually recursive Dec's, so we need to process every
-- binding occurrence first, get one big extended parameter data structure, and
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
             , free    :: [Var]  -- These occur free (implies dependency)
             , tbinds  :: [Var]  -- Binds these (in type space)
             , tfree   :: [Var]  -- these type vars occur free (implies dependency)
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

addFree bound v x = if elem v bound || elem v fs then x else x{free = v : fs}
  where fs = free x
addBind v x = x {binds = v : binds x}
addDepend v x = x {depends = v : depends x}
addBindT ts x = x {tbinds = union ts (tbinds x)}
addFreeT ts x = x {tfree = union ts (tfree x)}
addFreeTname nm x = x {tfree = union [Global nm] (tfree x)}

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

proto (Global ('%':s)) = Global ("%::"++s)
proto (Global s) = Global ("::"++s)
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
  boundBy ts@(TypeSig loc [v] t) =
        if isTyCon v then FX [] [] [] (proto v :nub binds) [v]
                     else if isTypeFun ts then FX [] [] [] (proto v':nub binds) [v']
                     else FX [proto v] (v:ff) [] (nub binds) []
     where (FX _ _ ff tbs tfs) = vars [] t emptyF
           (binds,free) = partition typVar tfs
           isTyCon (Global (x:xs)) = isUpper x
           isTyCon _ = False
           preflag (Global nm) = Global ('%':nm)
           v' = preflag v
  boundBy (Prim l (Explicit nm t)) = FX [nm] [] [] [] constrs
     where (FX _ _ _ tbs tfs) = vars [] t emptyF
           (vs,constrs) = partition typVar tfs

  boundBy (Data l b 0 nm sig vs cs ders) = bindDs ders (FX (map get cs) [] [] [nm] [proto nm])
     where get (Constr loc skol c ts eqs) = c
  boundBy (GADT loc isProp nm knd cs ders _)| definesValueConstr knd =
            bindDs ders (FX (map get cs) [] [] [nm] [proto nm])
     where get (loc,c,free,preds,typ) = c

  boundBy (Data l b _ nm sig vs cs ders) = bindDs ders (FX [] [] [] (nm : map get cs) [proto nm])
     where get (Constr loc skol c ts eqs) = c
  boundBy (GADT loc isProp nm knd cs ders _) | not(definesValueConstr knd) =
          bindDs ders (FX [] [] [] (nm : map get cs) [proto nm])
     where get (loc,c,free,preds,typ) = c

  boundBy (Import s vs) = emptyF
  boundBy (TypeSyn loc nm args ty) = FX [] [] [] [Global nm] [proto (Global nm)]
  boundBy (TypeFun loc nm ty ms) = FX [] [] [] [Global nm'] [proto (Global nm')]
    where nm' = '%':nm
  boundBy (AddTheorem _ _) = emptyF
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

  vars bnd (GADT loc isProp nm knd cs _ _) =
       vars bnd knd . varsL bnd cs

  vars bnd (TypeSig loc [v] t) = addFreeT (nub free)
     where (FX _ _ _ tbs tfs) = vars bnd t emptyF
           (binds,free) = partition typVar tfs
  vars bnd (TypeSyn loc nm args ty) = underTs (map fst args) (vars bnd ty)
  vars bnd (TypeFun loc nm k ms) = varsL bnd ms
  vars bnd (AddTheorem loc xs) = varsL bnd xs
  vars bnd _ = id

instance Vars (Var,Maybe Exp) where
  vars bnd (v,Nothing) = vars bnd v
  vars bnd (_,Just e) = vars bnd e

instance Vars (Loc,Var,[([Char],PT)],[PPred],PT) where
  vars bnd (loc,c,free,preds,typ) =
    varsL bnd preds . vars bnd typ

instance Vars ([PT],PT) where
  vars bnd (args,body) = addFreeT constrs . underTs vs (vars bnd body)
    where (FX _ _ _ _ argfree) = varsL bnd args emptyF
          (vs,constrs) = partition typVar argfree

instance Vars a => Vars (Maybe a) where
  vars bnd (Just x) = vars bnd x
  vars bnd Nothing = id

-- Organize and sequence the two steps
-- Combine "binds" "depends" "tbinds" from step 1
-- with "free" and "tfree" of second step.

instance Vars [Dec] where
  vars bnd ds x = FX vbnd deps fs tbnd (tfs ++ tfs2)         -- Combine
    where (FX vbnd deps _ tbnd tfs2) = boundBy ds            -- Step 1
          (FX _ _ fs _ tfs) = foldr (vars (vbnd++bnd)) x ds  -- Step 2

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
  vars bnd (Rel' nm ts) = addFreeTname nm . vars bnd ts

instance Vars PT where
  vars bnd (TyVar' s) = addFreeTname s
  vars bnd (TyCon' s _) = addFreeTname s
  vars bnd (TyApp' x y) = vars bnd x . vars bnd y
  vars bnd (Kinded x y) = vars bnd x . vars bnd y
  vars bnd (Rarrow' x y) = vars bnd x . vars bnd y
  vars bnd (Karrow' x y) = vars bnd x . vars bnd y
  vars bnd (TyFun' (TyVar' f :xs)) = addFreeTname ('%':f) . varsL bnd xs
  vars bnd (w@(TyFun' (f :xs))) = error ("Bad type function: "++show f++" -- "++show w)
  vars bnd (Star' _ _) = id
  vars bnd (Forallx q ss eqs t) = underTs args (vars bnd t) . underTs args (varsL bnd eqs)
    where args = (map (Global . fst3) ss)
          fst3 (a,b,c) = a
  vars bnd (Tlamx s t) = underTs [Global s] (vars bnd t)
  vars bnd (AnyTyp) = id
  vars bnd (Ext a) = depExt a . varsL bnd (extList a)
  vars bnd (PolyLevel vs x) = underTs (map Global vs) (vars bnd x)

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
  vars bnd (ExtP a) = depExt a . varsL bnd (extList a)

instance Vars Var where
  vars bnd v = addFree bnd v

instance Vars Exp where
  vars bnd (Var v) = addFree bnd v
  vars bnd (Lit _) = id
  vars bnd (Sum _ e) = vars bnd e
  vars bnd (Prod e1 e2) = (vars bnd e1) . (vars bnd e2)
  vars bnd (App e1 e2) = (vars bnd e1) . (vars bnd e2)
  vars bnd (Lam ps e xs) = underBinder ps (\ bnd -> vars bnd e) bnd
  vars bnd (Let ds e) = underBinder ds (\ bnd -> vars bnd e) bnd
  vars bnd (Circ vs e ds) = underBinder ds (\ bnd -> vars bnd e) bnd
  vars bnd (Case e ms) = (vars bnd e) . (varsL bnd ms)
  vars bnd (Do (bindE,failE) ss) = vars bnd ss . vars bnd failE . vars bnd bindE
  vars bnd (CheckT x) = vars bnd x
  vars bnd (Lazy x) = vars bnd x
  vars bnd (Exists x) = vars bnd x
  vars bnd (Bracket e) = vars bnd e
  vars bnd (Escape e) = vars bnd e
  vars bnd (Reify s v) = id
  vars bnd (Ann x t) = vars bnd x
  vars bnd (ExtE x) = depExt x . varsL bnd (extList x)

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
-- two distict name spaces, we "flag" names in the type name space
-- so they'll be distinct.

freeOfDec :: Dec -> ([Var],[Var])
freeOfDec d = (bound,deps)
  where x = vars [] [d] emptyF
        bound = binds x ++ map flagNm (filter (not . typVar) (tbinds x))
        deps = free x ++ depends x ++ map flagNm (tfree x)

flagNm g@(Global x) = if flagged g then g else Global ('%':x)
flagNm g = g

flagged (Global ('%':s)) = True
flagged (Alpha ('%':s) n) = True
flagged _ = False

declBindsFree vars d = binds(boundBy d)

-- expFV bound (Var x) = if x `elem` bound then [] else [x]

-- ======================================================================
-- Term Equality for testing

matchEQ:: (Eq a,Eq b, Eq c) => (Match a b c)-> (Match a b c) -> Bool
matchEQ (loc1,pat1,body1,ds1) (loc,pat,body,ds) = pat1==pat && body1==body && ds1==ds

listEq f [] [] = True
listEq f (x:xs) (y:ys) = f x y && listEq f xs ys
listEq f _ _ = False


instance Eq Exp where
  (Var a) == (Var b) = a == b
  (Lit a) == (Lit b) = a == b
  (Sum i1 e1) == (Sum i2 e2) = i1==i2 && e1==e2
  (Prod e1 e2) == (Prod e3 e4) = e1==e3 && e2==e4
  (App e1 e2) == (App e3 e4) = e1==e3 && e2==e4
  (Lam pts1 e1 vis1) == (Lam pts2 e2 vis2) =
    pts1==pts2 && e1==e2 --what's vis for?
  (Let ds1 e1) == (Let ds2 e2) = ds1==ds2 && e1==e2
  (Circ vs1 e1 ds1) == (Circ vs2 e2 ds2) =
    vs1==vs2 && e1==e2 && ds1==ds2
  (Case e1 ms1) == (Case e2 ms2) = e1==e2 && listEq matchEQ ms1 ms2
  (Do (bE1,fE1) ss1) == (Do (bE2,fE2) ss2) = bE1==bE2 && fE1==fE2 && ss1 == ss2
  (CheckT e1) == (CheckT e2) = e1==e2
  (Lazy e1) == (Lazy e2) = e1==e2
  (Exists e1) == (Exists e2) = e1==e2
  (Bracket e1) == (Bracket e2) = e1==e2
  (Escape e1) == (Escape e2) = e1==e2
  (Reify s1 v1) == (Reify s2 v2) = s1==s2 && v1==v2
  (Ann e1 pt1) == (Ann e2 pt2) = e1==e2 && pt1==pt2
  (ExtE x) == (ExtE y) = x==y
  _ == _ = False

instance Eq Pat where
  (Plit l1) == (Plit l2) = l1==l2
  (Pvar v1) == (Pvar v2) = v1==v2
  (Pprod p1 p2) == (Pprod p3 p4) = p1==p3 && p2==p4
  (Psum i1 p1) == (Psum i2 p2) = i1==i2 && p1==p2
  (Pexists p1) == (Pexists p2) = p1==p2
  (Paspat v1 p1) == (Paspat v2 p2) = v1==v2 && p1==p2
  Pwild == Pwild = True
  (Pcon v1 ps1) == (Pcon v2 ps2) = v1==v2 && ps1==ps2
  (Pann p1 pt1) == (Pann p2 pt2) = p1==p2 && pt1==pt2
  (ExtP x) == (ExtP y) = x==y
  _ == _ = False

instance Eq Dec where
  (Fun _ v1 Nothing ms1) == (Fun _ v2 Nothing ms2) = v1==v2 && listEq matchEQ ms1 ms2
  (Fun _ v1 (Just pt1) ms1) == (Fun _ v2 (Just pt2) ms2) = v1==v2 && pt1==pt2 && listEq matchEQ ms1 ms2
  (Val _ p1 b1 ds1) == (Val _ p2 b2 ds2) =
     p1==p2 && b1==b2 && ds1==ds2
  (Pat _ v1 vs1 p1) == (Pat _ v2 vs2 p2) = v1==v2 && vs1==vs2 && p1==p2
  (TypeSig _ v1 pt1) == (TypeSig _ v2 pt2) = v1==v2 && pt1==pt2
  (Prim _ (Explicit v1 pt1)) == (Prim _ (Explicit v2 pt2)) = v1==v2 && pt1==pt2
  (Data _ b1 str1 v1 Nothing targ1 cs1 ders1) == (Data _ b2 str2 v2 Nothing targ2 cs2 ders2) =
     b1==b2 && str1==str2 && v1==v2 && targ1==targ2 && cs1==cs2 && ders1==ders2
  (Data _ b1 str1 v1 (Just pt1) targ1 cs1 ders1) == (Data _ b2 str2 v2 (Just pt2) targ2 cs2 ders2) =
     b1==b2 && str1==str2 && v1==v2 && pt1==pt2 && targ1==targ2 && cs1==cs2 && ders1==ders2
  (GADT x1 x2 x3 x4 x5 x6 x7) == (GADT y1 y2 y3 y4 y5 y6 y7) =
     x2==y2 && x3==y3 && x4==y4 && map f x5== map f y5
       where f (loc,v,cs,ps,r) = (v,cs,ps,r)
  (Flag v1 v2) == (Flag v3 v4) = v1==v3 && v2==v4
  (Reject s1 ds1) == (Reject s2 ds2) = s1==s2 && ds1==ds2
  (Import s1 vs1) == (Import s2 vs2) = s1==s2 && vs1==vs2
  (TypeSyn _ s1 targs1 pt1) == (TypeSyn _ s2 targs2 pt2) =
     s1==s2 && targs1==targs2 && pt1==pt2
  (TypeFun _ s1 Nothing xs1) == (TypeFun _ s2 Nothing xs2) =
     s1==s2 && xs1==xs2
  (TypeFun _ s1 (Just pt1) xs1) == (TypeFun _ s2 (Just pt2) xs2) =
     s1==s2 && pt1==pt2 && xs1==xs2
  _ == _ = False

instance (Eq p, Eq e, Eq d) => Eq (Stmt p e d) where
  (BindSt _ p1 e1) == (BindSt _ p2 e2) = p1==p2 && e1==e2
  (LetSt _ ds1) == (LetSt _ ds2) = ds1==ds2
  (NoBindSt _ e1) == (NoBindSt _ e2) = e1==e2
  _ == _ = False

instance Eq V where
  Vlit v1 == Vlit v2 = v1==v2
  _ == _ = True -- need more?

instance Eq Constr where
  (Constr _ targs1 v1 pts1 Nothing) == (Constr _ targs2 v2 pts2 Nothing) =
    targs1==targs2 && v1==v2 && pts1==pts2
  (Constr _ targs1 v1 pts1 (Just pps1)) == (Constr _ targs2 v2 pts2 (Just pps2)) =
    targs1==targs2 && v1==v2 && pts1==pts2 && pps1 == pps2
  _ == _ = False

instance Eq e => Eq (Body e) where
  (Guarded es1) == (Guarded es2) = es1==es2
  (Normal e1) == (Normal e2) = e1==e2
  Unreachable == Unreachable = True
  _ == _ = False

-- =======================================================================
-- Syntax into Documents

ppSig Nothing _ = PP.empty
ppSig (Just pt) v = ppVar v <+> text "::" <+> ppPT pt

ppArg (v,AnyTyp) = ppVar v
ppArg (v,pt) = PP.parens $ ppVar v <> text "::" <> ppPT pt

ppStrat 0 = text "data"
ppStrat 1 = text "kind"
ppStrat 2 = text "sort"
ppStrat 3 = text "class"
ppStrat n = text "data@" <> PP.int n

data Pos = Front | Back

myPP f _ _ [] = PP.empty
myPP f _ _ [x] = x
myPP f Front s (x:xs) = f (x:(map (\ y -> s <> y) xs))
myPP f Back s xs = f ((map (\ y -> y <> s) (init xs)) ++ [last xs])

ppWhere [] = PP.empty
ppWhere ds = text "where" <+> PP.vcat (map ppDec ds)

ppClause (_,ps,b@(Guarded _) ,ds) = PP.sep [PP.sep [PP.hsep (map ppPat ps), ppBody b], PP.nest 2 $ ppWhere ds]
ppClause (_,ps,b ,ds) = PP.vcat [PP.sep [PP.sep (map ppPat ps) <+> PP.equals, ppBody b], PP.nest 2 $ ppWhere ds]

ppImport (VarImport v) = ppVar v
ppImport (SyntaxImport s y) = text ("deriving "++s++"("++y++")")

ppParensCommaSep x = PP.parens (PP.sep (PP.punctuate PP.comma x))

ppDec :: Dec -> Doc
ppDec dec =
  case dec of
    Fun _ v Nothing ms -> PP.vcat $ map ((ppVar v) <+>) (map ppClause ms)
    Fun _ v (Just pt) ms -> PP.vcat ((text "*" <> ppVar v <+> text "::" <+> ppPT pt):(map ((ppVar v) <+>) (map ppClause ms)))
    Val _ p b ds -> PP.vcat [PP.sep [ppPat p <+> PP.equals, PP.nest 2 $ ppBody b], PP.nest 2 $ ppWhere ds]
    Pat _ v vs p  -> text "pattern" <+> ppVar v <+> PP.hsep (map ppVar vs) <+> PP.equals <+> ppPat p
    TypeSig _ v pt -> PP.sep (PP.punctuate PP.comma (map ppVar v)) <+> text "::" <+> ppPT pt
    Prim _ bindings -> text "primitive" <+> ppBindings bindings
      where ppBindings (Explicit v pt) = ppVar v <+> text "::" <+> ppPT pt
            ppBindings (Implicit vs) = text "import" <+> ppParensCommaSep (map ppVar vs)
    Data _ b n v sig args cs []   -> PP.vcat [ppSig sig v,
                                     ppStrat n <+> ppVar v <+>
                                     PP.hsep (map ppArg args) <+> PP.equals <+>
                                     myPP PP.vcat Front (PP.nest (-2) (text "| ")) (map ppConstr cs)]
    Data _ b n v sig args cs ders   -> PP.vcat [ppSig sig v,
                                       ppStrat n <+> ppVar v <+>
                                       PP.hsep (map ppArg args) <+> PP.equals <+>
                                       myPP PP.vcat Front (PP.nest (-2) (text "| ")) (map ppConstr cs),
                                       PP.nest 2 $ text "deriving" <+> PP.parens (myPP PP.hsep Back PP.comma (map ppDeriv ders))]
    GADT loc isprop nm kind cs ders exts ->
      (text "data" <+> ppVar nm <> text "::" <+> ppPT kind <+> text "where") $$
      (PP.nest 3 (PP.vcat (map ppCs cs))) $$
      (PP.nest 2 (text "deriving" <+> PP.parens (myPP PP.hsep Back PP.comma (map ppDeriv ders))))
    Flag v1 v2 -> text "flag" <+> ppVar v1 <+> ppVar v2
    Reject s ds -> PP.vcat [text "##test" <+> PP.doubleQuotes (text s), PP.nest 2 $
                   (myPP PP.vcat Back PP.empty (map ppDec ds))]
    Import s Nothing -> text "import" <+> PP.doubleQuotes (text s)
    Import s (Just vs) -> text "import" <+> PP.doubleQuotes (text s) <> PP.parens (myPP PP.hsep Back PP.comma (map ppImport vs))
    TypeSyn _ s args pt -> PP.sep [text ("type "++s) <+> PP.hsep (map ppArg args) <+> PP.equals,ppPT pt]
    TypeFun _ s Nothing ms -> PP.vcat ((text s <> text "::<no prototype>\n"):f1 ms)
    TypeFun _ s (Just pt) ms -> PP.vcat ((text (s++" :: ") <> ppPT pt):(f1 ms))
    AddTheorem loc xs -> text "theorem " <> (PP.vcat (map f xs))
     where f (x,Nothing) = ppVar x
           f (x,Just e) = ppVar x <+> PP.equals <+> ppExp e
   where
      f (v,pts) = ppVar v <+> PP.hsep (map ppPT pts)
      f1 ms = (map f2 ms)
      f2 (pts,pt) = PP.braces (PP.hsep (map ppPT pts)) <+> PP.equals <+> ppPT pt
ppCs (loc,name,vars,preds,typ) =
   PP.sep [(ppVar name <> text "::"),PP.nest 3 (PP.sep [all vars,quals preds,ppPT typ])]
  where all [] = PP.empty
        all xs = text "forall" <+> PP.fsep (map showM xs) <+> text "."
        quals [] = PP.empty
        quals xs = PP.nest 2 (PP.parens (PP.fsep (sepBy ppPred "," xs)) <+> text "=>")
        showM (v,AnyTyp) = text v
        showM (v,pt) = PP.parens $ text v <> text "::" <> ppPT pt

sepBy f comma [] = []
sepBy f comma [x] = [f x]
sepBy f comma (x:xs) = ((f x) <> (text comma)):sepBy f comma xs

ppConstr (Constr _ args v pts mpps) =
  exists args <+> ppVar v <+> PP.vcat [PP.hsep (map parenT pts), eqf mpps]
  where exists [] = PP.empty
        exists ns = text "forall" <+> PP.hsep (map showM ns) <+> text "."
        parenT (x @ (TyApp' y _)) = g (root' y) x
          where g (TyCon' "(,)" _) y = ppPT y
                g (TyCon' "(+)" _) y = ppPT y
                g (TyCon' "[]" _) y = ppPT y
                g x y = PP.parens $ ppPT y
        parenT (x@(Rarrow' _ _)) = PP.parens $ ppPT x
        parenT (x@(Forallx _ _ _ _)) = PP.parens $ ppPT x
        parenT x = ppPT x
        eqf Nothing = PP.empty
        eqf (Just xs) = text " where" <+> myPP PP.sep Back PP.comma (map ppPred xs)
        root' (TyApp' x y) = root' x
        root' x = x

showM (v,AnyTyp) = ppVar v
showM (v,pt) = PP.parens $ ppVar v <> text "::" <> ppPT pt

ppVar (Global s) = text s
ppVar (Alpha s1 n) = text (short (name2Int n))

ppPred (Equality' x y) = PP.hsep [ppPT x, PP.equals, ppPT y]
ppPred (Rel' _ t) = ppPT t

expList (Prod x y) = x : expList y
expList x = [x]

patList (Pprod x y) = x : patList y
patList x = [x]


ppPat pat =
  case pat of
    Plit l -> ppLit l
    Pvar v -> ppVar v
    Pprod e1 e2 ->
      case patList pat of
        xs -> ppParensCommaSep (map ppPat xs)
    Psum L p -> PP.parens $ text "L" <+> ppPat p
    Psum R p -> PP.parens $ text "R" <+> ppPat p
    Pexists p -> PP.parens $ text "Ex" <+> ppPat p
    Paspat v p -> PP.parens $ ppVar v <> text "@" <> ppPat p
    Pwild -> text "_"
    Pcon v [] -> ppVar v
    Pcon (Global ":") (p1:ps) -> PP.parens $ ppPat p1 <+> text  ":" <+> PP.hsep (map ppPat ps)
    Pcon v ps -> PP.parens $ ppVar v <+> PP.hsep (map ppPat ps)
    Pann p pt -> ppPat p <+> text "::" <+> ppPT pt
    ExtP p -> ppExt ppPat p

ppLit l =
  case l of
    Int i -> PP.int i
    Char c -> PP.quotes $ PP.char c
    Unit -> text "()"
    Symbol s -> text "'" <> text (show s)
    ChrSeq s -> text "#" <> text s
    Tag s -> text "`" <> text s
    Float f -> PP.float f
    CrossStage v -> text "%constant"

ppBody b =
  case b of
    Guarded pes -> text "|" <+> myPP PP.vcat Front (PP.nest (-2) $ text "| ") (map f pes)
      where f (e1,e2) = ppExp e1 <+> PP.equals <+> ppExp e2
    Normal e -> ppExp e
    Unreachable -> text "unreachable"

ppParFun (x@(App _ _)) = ppExp x
ppParFun x = ppParExp x

ppParExp (x @ (Var _)) = ppExp x
ppParExp (x @ (Lit _)) = ppExp x
ppParExp (x @ (Prod _ _)) = ppExp x
ppParExp (x @ (Escape _)) = ppExp x
ppParExp (x @ (Bracket _)) = ppExp x
ppParExp (x @ (Reify s v)) = ppExp x
ppParExp (x @ (ExtE _)) = ppExp x
ppParExp x = case isList x of
             Just z -> ppList z
             Nothing -> PP.parens $ ppExp x

ppList xs | all isChar xs = PP.doubleQuotes $ text (map charOf xs)
ppList xs = PP.brackets(PP.fsep (sepBy ppExp "," xs))    -- text (show xs)

isOp (App (App (Var (Global f)) x) y) = if infixp f then Just (x,f,y) else Nothing
isOp (App (App (Reify s v) x) y) = if infixp s then Just (x,s,y) else Nothing
isOp _ = Nothing

ppExp e =
  case e of
    Var v -> ppVar v
    Lit l -> ppLit l
    Sum L e -> PP.parens $ text "L" <+> ppExp e
    Sum R e -> PP.parens $ text "R" <+> ppExp e
    Prod e1 e2 ->
      case expList e of
        xs -> ppParensCommaSep (map ppExp xs)
    x @ (App e1 e2) ->
      case (tryL x [Fpair isList ppList, Fpair isOp ppOp]) of
        Just ans -> ans
        Nothing -> (ppParFun e1) <+> (ppParExp e2)
      where ppOp (a,b,c) = (ppParFun a) <+> text b <+> ppParFun c
    Lam ps e vis -> text "\\" <+> PP.sep[PP.hsep (map ppPat ps)<+> text "->", PP.nest 3 (ppExp e)]
    Let ds e -> PP.vcat [text "let" <+> PP.vcat (map ppDec ds),PP.sep [text "in",ppExp e]]
    Circ vs e ds -> PP.parens $ PP.vcat [PP.sep [text "circuit",
                                        PP.parens (myPP PP.hsep Back PP.comma (map ppVar vs)),
                                        ppExp e], PP.nest 2 (ppWhere ds)]
                    --PP.vcat ((text "where"):(zipWith ((<+>).((flip $ (<+>))) PP.equals) (map ppVar vs) (map ppDec ds))))
    Case e ms -> (text "case" <+> ppParExp e <+> text "of") $$
                 (PP.nest 2 (PP.vcat (map ppMatch ms)))
    Do _ ss -> text "do" <+> PP.braces (PP.space <> myPP PP.vcat Front (PP.nest (-2) $ text "; ") (map ppStmt ss) <> PP.space)
    CheckT e -> PP.parens $ text "Check" <+> ppExp e
    Lazy e -> PP.parens $ text "lazy" <+> ppExp e
    Exists e -> PP.parens $ text "Ex" <+> ppExp e
    Bracket e -> PP.brackets $ text "|" <+> ppExp e <+> text "|"
    Escape (Var v) -> text "$" <> ppVar v
    Escape e -> text "$" <> PP.parens (ppExp e)
    Reify s (Vlit c) -> ppLit c
    Reify s v -> text $ '%':s
    Ann e pt -> PP.parens $ ppExp e <> text "::" <> ppPT pt
    ExtE x -> ppExt ppExp x

ppMatch (_,p,body,d) = PP.sep [ppPat p <+> text "->",PP.nest 2 (ppBody body),PP.nest 2 (ppWhere d)]

ppStmt s =
  case s of
    BindSt _ p e -> ppPat p <+> text "<-" <+> ppExp e
    LetSt _ ds -> text "let" <+> PP.vcat (map ppDec ds)
    NoBindSt _ e -> ppExp e

-- Print Type

needsParens (TyApp' (TyCon' "[]" _) x) = False
needsParens (TyApp' (TyApp' (TyCon' "(,)" _) _) _) = False
needsParens (TyApp' (TyApp' (TyCon' "(+)" _) _) _) = False
needsParens (TyApp' _ _) = True
needsParens (Rarrow' _ _) = True
needsParens (Karrow' _ _) = True
needsParens (Forallx _ _ _ _) = True
needsParens _ = False

ppAll (x@(Forallx _ _ _ _)) = PP.parens(ppPT x)
ppAll x = ppPT x

ppPT x =
  case x of
    PolyLevel ns x -> text "level " <> PP.sep (map text ns) <> text " . " <> ppPT x
    TyVar' s -> text s
    Rarrow' x y -> PP.hsep [ppAll x, text "->", ppAll y]
    Karrow' x y -> PP.parens $ PP.hsep [ppPT x, text "~>", ppPT y]
    TyApp' (TyApp' (TyCon' "(,)" _) x) y ->
        PP.sep[PP.lparen <> ppPT x,PP.comma <> ppPT y,PP.rparen]
    TyApp' (TyApp' (TyCon' "(+)" _) x) y ->
        PP.sep[PP.lparen <> ppPT x,text "+" <> ppPT y,PP.rparen]
    TyApp' (TyApp' (TyCon' "(->)" _) x) y ->
        PP.sep[ppPT x <+> text "->",PP.nest 1 (ppPT y)]
    TyApp' (TyApp' (TyCon' "Equal" _) x) y ->
        PP.lparen <> text "Equal" <+> PP.sep[ppPT x <+> PP.nest 7 (ppPT y)] <> PP.rparen
    TyApp' (TyCon' "[]" _) x -> PP.brackets (ppPT x)
    TyApp' f x | needsParens x -> (ppPT f) <+> (PP.parens (ppPT x))
    TyApp' f x -> (ppPT f) <+> (ppPT x)
    Kinded f x -> PP.parens (ppPT f <> text "::" <+> ppPT x)
    TyFun' xs -> PP.braces(PP.hsep (map ppPT xs))
    TyCon' s Nothing -> text s
    TyCon' s (Just(0,n)) -> text (s++"_"++n)
    TyCon' s (Just(i,n)) -> text (concat[s,"_(",show i,"+",n,")"])
    Star' n Nothing -> text "*" <> PP.int n
    Star' 0 (Just n) -> text "*" <> text n
    Star' k (Just n) -> text "*(" <> PP.int k <> text ("+"++n++")")
    Forallx q [] [] t -> ppPT t
    Forallx q vs [] t ->
        ppQ q <+> PP.sep [PP.sep (ppV vs) <+> text ".", ppPT t]
    Forallx q vs [p] t ->
        ppQ q <+> PP.sep [PP.sep (ppV vs) <+> text "."
                         ,ppP p <+> text "=>"
                         ,ppPT t]
    Forallx q vs ps t ->
        ppQ q <+> PP.sep [PP.sep (ppV vs) <+> text "."
                         ,PP.parens (myPP PP.sep Back PP.comma (map ppP ps)) <+> text "=>"
                         ,ppPT t]
    AnyTyp -> text "*?"
    Ext x -> ppExt ppPT x

ppQ All = text "forall"
ppQ Ex = text "exists"

--temp ppV
ppV [(s,AnyTyp,q)] = [text s <> shq q] -- <+> text ". "]
ppV ((s,AnyTyp,q):xs) = (text s <> shq q):(ppV xs)
ppV [(s,k,q)] = [PP.parens $ text s <> shq q <+> text "::" <+> ppPT k] -- <+> text ". "]
ppV ((s,k,q):xs) = (PP.parens $ text s <> shq q <+> text "::" <+> ppPT k):(ppV xs)
ppV [] = [PP.empty]
shq All = PP.empty
shq Ex = text "'"

ppP (Equality' x y) = PP.hsep [ppPT x, PP.equals, ppPT y]
ppP (Rel' _ t) = ppPT t

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

---------------------------------------------------------
-- Showing a thing with multiple ways to show it

data Fpair x y = forall t . Fpair (x -> Maybe t) (t -> y)

tryL :: a -> [Fpair a b] -> Maybe b
tryL x [] = Nothing
tryL x ((Fpair f g):fs) =
   case f x of
      Just x -> Just(g x)
      Nothing -> tryL x fs

instance Show Lit where
  show l = render(ppLit l)
instance Show Pat where
  show p = render(ppPat p)
instance Show Dec where
  show d = render(ppDec d)
instance Show Exp where
  show d = render(ppExp d)
instance Show (Body Exp) where
  show b = render(ppBody b)
instance Show (Stmt Pat Exp Dec) where
  show s = render(ppStmt s)

