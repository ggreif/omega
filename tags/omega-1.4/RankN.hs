-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Tue Feb 27 21:04:24 Pacific Standard Time 2007
-- Omega Interpreter: version 1.4

{-# OPTIONS_GHC -fglasgow-exts -fallow-undecidable-instances #-}
module RankN where

import Bind
-- import IOExts
import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import System.IO.Unsafe(unsafePerformIO)
import Monads
import Monad(when,foldM)
import List((\\),nub,union,unionBy,sortBy,groupBy,partition,find)
import Auxillary(Loc(..),plist,plistf,extendM,foldrM,makeNames
                ,DispInfo(..),Display(..),useDisplay,initDI
                ,disp2,disp3,disp4,disp5,dispL,DispElem(..),displays,dv,tryDisplay
                ,maybeM)
import ParserAll  -- This for defining the parser for types
-- To import ParserAll you must define CommentDef.hs and TokenDef.hs
-- These should be in the same directory as this file.
import Char(isLower)

import qualified Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.HughesPJ(Doc,text,int,(<>),(<+>),($$),($+$),render)

import SyntaxExt
------------------------------------------------------
-- The Z type is used inside of Display objects as the index

data Z = ZVar Name Kind
       | ZTv TcTv

instance Show Z where
  show (ZVar n k) = show (TyVar n k)
  show (ZTv x) = show(TcTv x)

instance Eq Z where
  (ZVar a b) == (ZVar m n) = (TyVar a b) == (TyVar m n)
  (ZTv x) == (ZTv y) = (TcTv x) == (TcTv y)
  x == y = False

dn:: Display a Z => a -> DispElem Z
dn x = Dn x

disp0:: DispInfo Z
disp0 = initDI
------------------------------------------------------------
-- warnings and failures that communicate through the implicit display

-- The implicit display
dispRef = unsafePerformIO(newIORef disp0)

warnM elems =
  do { d <- readRef dispRef
     ; let (d2,message) = displays d elems
     ; outputString message
     ; writeRef dispRef d2 }

failD :: TyCh m => Int -> [DispElem Z] -> m b
failD n = failK "" n

failK :: TyCh m => String -> Int -> [DispElem Z] -> m b
failK k n elems =  failDd k n elems

failDd k n elems =
   do { d <- readRef dispRef;
      ; let (d2,s) = displays d elems
      ; writeRef dispRef d2
      ; failP k n s }


failM n xs =  failDd "" n xs

failMD n d xs = failDd "" n d xs

whenM True elems = warnM elems
whenM False elems = return()

-- Versions that don't use the implicit display

warnP elems = warnPD disp0 elems

warnPD d1 elems = outputString message >> return d2
  where (d2,message) = displays d1 elems

whenP True d  elems = warnPD d elems
whenP False d elems = return d

--------------------------------------------------------------------
-- Levels

data Level = LvZero | LvSucc Level | TcLv TcLv
  deriving Eq

data TcLv = LvMut Uniq (IORef (Maybe Level)) | LvVar Name

instance Eq TcLv where
  (LvMut u1 _) == (LvMut u2 _) = u1==u2
  (LvVar n1) == (LvVar n2) = n1==n2
  x == y = False

lv 0 = LvZero
lv (n+1) = LvSucc (lv n)

fromLevel LvZero = Just 0
fromLevel (LvSucc x) = fmap (+1) (fromLevel x)
fromLevel (TcLv n) = Nothing

zonkLv :: TyCh m => Level -> m Level
zonkLv x = do { a <- pruneLv x; walk a }
 where walk (LvSucc x) = do { y<- zonkLv x; return(LvSucc y)}
       walk x = return x

pruneLv :: TyCh m => Level -> m Level
pruneLv (t@(TcLv(LvMut uniq ref))) =
  do { x <- readRef ref
     ; case x of
          Nothing -> return t
          Just y -> do {a <- pruneLv y; writeRef ref (Just a); return a}}
pruneLv x = return x

unifyLevel :: TyCh m => Level -> Level -> m ()
unifyLevel x y = do { a <- pruneLv x; b <- pruneLv y; walk (a,b)}
  where walk (LvZero,LvZero) = return()
        walk (LvSucc x,LvSucc y) = unifyLevel x y
        walk (TcLv v,TcLv u) | u==v = return()
        walk (TcLv(v@(LvMut u r)),y) = unifyLvVar v y
        walk (y,TcLv(v@(LvMut u r))) = unifyLvVar v y
        walk (x,y) = failD 1 [Ds "Levels don't match ",Dd x,Ds " =/= ",Dd y]

levelVars x = do { a <- pruneLv x; walk a }
  where walk (TcLv (v@(LvMut u r))) = return (Just v)
        walk (LvSucc x) = levelVars x
        walk _ = return Nothing

unifyLvVar (v@(LvMut u r)) level =
  maybeM (levelVars level)
         (\ u -> if u==v
                 then failD 1 [Ds "Level occurs check"]
                 else writeRef r (Just level))
         (writeRef r (Just level))


 ---  FIX ME
instance TyCh m => TypeLike m Level where
  sub env@(ns,vs,cs,ls) x = subLevel ls x
  zonk x = zonkLv x
  get_tvs x =
     do { zs <- levelVars x;
        ; case zs of
           Nothing -> return([],[])
           Just v -> return([],[v])}
  --nf x = zonkLv x

subLevel env x = do { a <- pruneLv x; walk a }  where
   walk (t@(TcLv v)) = case lookup v env of
                         Nothing  -> return t
                         Just l -> return l
   walk (LvSucc x) = do { a <- subLevel env x; return(LvSucc a) }
   walk x = return x

varsOfLevel (TcLv (v@(LvMut u r))) = ([],[],[v])
varsOfLevel (LvSucc x) = varsOfLevel x
varsOfLevel x = ([],[],[])

newLevel :: TyCh m => m Level
newLevel =
  do { ref <- newRef Nothing
     ; uniq <- nextInteger
     ; return(TcLv(LvMut uniq ref))}

newStar:: TyCh m => m Tau
newStar = do { n <- newLevel; return (Star n)}

newUniv:: TyCh m => m Tau
newUniv = do { k <- newStar; newTau (MK k)}

instance Ord Level where
  TcLv a `compare` TcLv b = compare a b
  TcLv _ `compare` _ = LT
  _ `compare` TcLv _ = GT
  LvZero `compare` LvZero = EQ
  LvZero `compare` LvSucc _ = LT
  LvSucc _ `compare` LvZero = GT
  LvSucc a `compare` LvSucc b = compare a b

instance Ord TcLv where
  LvMut u _ `compare` LvMut v _ = compare u v
  LvMut _ _ `compare` LvVar _ = LT
  LvVar _ `compare` LvMut _ _ = GT
  LvVar n `compare` LvVar m = compare n m

instance Show Level where
  show LvZero = "0"
  show (LvSucc l) = f 1 l
    where f n LvZero = show n
          f n (LvSucc l) = f (n+1) l
          f n l = "("++show n++"+"++show l++")"
  show (TcLv v) = show v

instance Show TcLv where
  show (LvVar n) = show n
  show (LvMut u r) = "?"++show u

instance Swap Level where
  swaps [] x = x
  swaps cs LvZero = LvZero
  swaps cs (LvSucc l) = LvSucc (swaps cs l)
  swaps cs (TcLv v) = TcLv (swaps cs v)

instance Swap TcLv where
  swaps cs (LvVar n) = LvVar (swaps cs n)
  swaps cs (LvMut u r) = LvMut u r

instance Exhibit (DispInfo Z) Level where
  exhibit env (TcLv (LvMut u r)) = useDisplay id env (ZTv(Tv u (Skol "") star))
  exhibit env (TcLv (LvVar n)) = useDisplay id env (ZVar n star)
  exhibit env LvZero = (env,"0")
  exhibit env (LvSucc x) = (f env x 1)
    where f env LvZero n = (env,show n)
          f env (LvSucc y) n = f env y (n+1)
          f env y n = let (env2,s) = exhibit env y in (env2,"("++show n++"+"++s++")")

-- End Levels
-- ================================================================
-- Types for implementing Omega Types

type Unifier = [(TcTv,Tau)]
type Uniq = Integer
type TRef = IORef (Maybe Tau)
data Pred = Equality Tau Tau | Rel Tau

equalityP (Equality _ _) = True
equalityP _ = False

makeRel tau =
  case equalPartsM tau of
    Nothing -> Rel tau
    Just(x,y) -> Equality x y

equalPartsM (TyApp (TyApp (TyCon sx _ "Equal" k) x) y) = return (x,y)
equalPartsM _ = fail "Not an Equality"

pred2Tau (Equality x y) = teq x y
pred2Tau (Rel x) = x

-----------------------------------------------------------

data PolyKind = K Sigma | Univ (Bind Name Sigma) -- some Type Constrs have polymorphic kinds!
data Kind = MK Tau
data L x = Nil x | Cons (Kind,Quant) (Bind Name (L x))
data Sigma = Forall (L ([Pred],Rho))

data Rho
  = Rarrow Sigma Rho
  | Rpair Sigma Sigma
  | Rsum Sigma Sigma
  | Rtau Tau

data Tau
  = TyVar Name Kind
  | TyApp Tau Tau
  | TyCon (SynExt String) Level String PolyKind
  | Star Level
  | Karr Tau Tau
  | TyFun {-Level-} String PolyKind [Tau]
  | TcTv TcTv
  | TySyn String Int [(Name,Kind)] [Tau] Tau
  | TyEx (L ([Pred],Tau))  -- anonymous existential types

data Flavor = Flexi TRef | Rigid Quant Loc String | Skol String

data TcTv = Tv Uniq Flavor Kind

data Expected a = Infer (IORef a) | Check a

data Quant = Ex | All deriving (Show,Eq)

instance Eq TcTv where (Tv i _ _) == (Tv j _ _) = i==j

instance Ord TcTv where compare (Tv i _ _) (Tv j _ _) = compare i j

type MGU = [(TcTv,Tau)]

---------------------------------------------------------------
-- Class definitions

class (HasIORef m,Fresh m,HasNext m,Accumulates m Pred
      ,TracksLoc m Z,HasOutput m) => TyCh m where
  envTvs :: m [TcTv]   -- extract free type vars from typing environment
  handleK :: (String -> Bool) -> Int -> m a -> (String -> m a) -> m a
  assume :: [Pred] -> MGU -> m a -> m a
  getBindings :: m MGU
  getDisplay :: m (DispInfo Z)
  solveSomeEqs :: TyCh m => (String,Rho) -> [Pred] -> m ([Pred],[(TcTv,Tau)])
  show_emit :: m Bool
  getTruths :: m[Pred]
  setTruths:: [Pred] -> m a -> m a
  currentLoc:: m Loc
  syntaxInfo:: m [SynExt String]

handleM n = handleK (const True) n

injectA loc_id preds =
  do { -- whenM (not(null preds)) [Ds "INJECTING ",Ds loc_id,Dd preds];
       injectAccum preds }

-- A type is TypeLike if it supports a few primitive operations
-- substitution, zonking, putting terms in normal form, and
-- finding the free type variables.

type ForAllArgs = [(Name,Kind,Quant)]

class TyCh m => TypeLike m t where
  sub :: ([(Name,Tau)],[(TcTv,Tau)],[(String,Tau)],[(TcLv,Level)]) -> t -> m t
  zonk :: t -> m t
  get_tvs :: t -> m ([TcTv], [TcLv])
  --nf :: t -> m t

class TyCh m => Quantify m t where
  for_all :: ForAllArgs -> t -> m Sigma

subst env t = sub (env,[],[],[]) t

substPred :: TyCh m => [(Name,Tau)] -> [Pred] -> m[Pred]
substPred [] xs = return xs
substPred env xs = mapM f xs
   where f (Equality x y) = do { a<-(subst env x); b<-(subst env y); return(Equality a b)}
         f (Rel ts) = do { a <- (subst env ts); return(makeRel a)}

-- A pair of types can be in the subsumption class if we can
-- ask if one is more polymorphic than another.

class TyCh m => Subsumption m x y where
  morepoly :: String -> x -> y -> m ()

-- a term type is Typable if one can check and infer types for it.
-- This is really a binary relation since the sort of "ty"
-- could be several things: like Rho, Sigma, or Kind

class (TypeLike m ty,TyCh m) => Typable m term ty where
  tc :: term -> Expected ty -> m term
  check :: term -> ty -> m term
  infer :: term -> m (ty,term)

  -- Default definitions for check and infer work if "tc"
  -- is defined, and the default definition for tc works if
  -- "infer" and "check" are defined. The idea is that you
  -- define either "tc" or ("check" and "infer"). Some
  -- instances, in particular for (Typable term Sigma)
  -- will define check and infer, and leave tc undefined
  -- because they behave differently than the defaults.
  check t k = tc t (Check k)
  infer t = do { ref <- newRef (error "DoNotPullOnMe")
               ; s <- tc t (Infer ref)
               ; t' <- readRef ref
               ; return(t',s)
               }
  tc x (Check t) = check x t
  tc x (Infer ref) =
     do { (ty,x') <- infer x; a <- zonk ty; writeRef ref a; return x'}



-- check that a list of terms all have the same expected type.

tcL :: Typable m term ty => [term] -> Expected ty -> m [term]
tcL [] expect = return []
tcL (t:ts) expect =
   do { t2 <- tc t expect; ts2 <- tcL ts expect; return(t2:ts2) }


-- check that a list of terms all match a multiple arg function type
-- checkArgs [t1,t2,t3] (a -> b -> c -> d) last ==>
-- tc t1 a; tc t2 b; tc t3 c; morepoly last d

checkArgs :: (Show term,Typable m term Sigma) => [term] -> Rho -> Expected Rho -> m [term]
checkArgs [] rho last = zap [] rho last
checkArgs (t:ts) rho last =
  do { (dom,rng) <- unifyFun rho
     ; s <- tc t (Check dom)
     ; ss <- checkArgs ts rng last
     ; return(s:ss)
     }

---------------------------------------------------------------
-- These functions make Rho objects in Normal form.
-- You should always use these rather than Rarrow, Rpair, and Rsum
-- when constructing Rho objects.

pair :: Sigma -> Sigma -> Rho
pair (Forall (Nil (_,Rtau x))) (Forall (Nil (_,Rtau y))) =
     Rtau (applyT[pairT,x,y])
pair x y = Rpair x y

arrow :: Sigma -> Rho -> Rho
arrow (Forall (Nil (_,Rtau x))) (Rtau y) = Rtau (tarr x y)
arrow x y = Rarrow x y

rsum :: Sigma -> Sigma -> Rho
rsum (Forall (Nil (_,Rtau x))) (Forall (Nil (_,Rtau y))) =
     Rtau (applyT[sumT,x,y])
rsum x y = Rsum x y

-----------------------------------------------------------------------
-- some example Sigma, Rho, and Tau type terms

applyT [t] = t
applyT [x,y] = TyApp x y
applyT (x : y : z) = applyT ((TyApp x y):z)

kindStar n = MK(Star n)
rhoStar n = Rtau(Star n)

star = MK(Star LvZero)
starR = Rtau(Star LvZero)
karr (MK x) (MK y) = MK(Karr x y)
kapp (MK x) (MK y) = MK(TyApp x y)

star_star = star `karr` star
star1 = MK(Star (LvSucc LvZero))
poly :: Kind -> PolyKind
poly (MK t) = K(simpleSigma t)

notEq x y = TyApp (TyApp notEqT x) y

poly1 :: Kind -> (Kind -> Kind) -> PolyKind
poly1 k f = K(Forall (Cons (k,All) (bind name1 (Nil([],Rtau term)))))
   where MK term = (f (MK(TyVar name1 k)))


unpoly :: PolyKind -> Kind
unpoly (K (Forall (Nil([],Rtau tau)))) = MK tau
unpoly x = error ("Can't turn the polykind "++show x++" into a normal kind.")

infixEqName = "(==)"
equalKind = K(Forall (Cons (star1,All) (bind name1 (Nil ([],ty)))))
   where k = TyVar name1 star1
         ty = Rtau(k `Karr` (k `Karr` propT))

intT =    TyCon Ox (lv 1) "Int" (poly star)
charT =   TyCon Ox (lv 1) "Char" (poly star)
boolT =   TyCon Ox (lv 1) "Bool" (poly star)
listT =   TyCon Ox (lv 1) "[]" (poly star_star)
parserT = TyCon Ox (lv 1) "Parser" (poly star_star)
unitT =   TyCon Ox (lv 1) "()" (poly star)
symbolT = TyCon Ox (lv 1) "Symbol" (poly star)
atomT =   TyCon Ox (lv 1) "Atom" kind4Atom
maybeT =  TyCon Ox (lv 1) "Maybe" (poly star_star)
monadT =  TyCon Ox (lv 1) "Monad" (poly (karr (star_star) star))
pairT =   TyCon (Px("","(,)")) (lv 1) "(,)" (poly (karr star (star_star)))
sumT =    TyCon Ox (lv 1) "(+)" (poly (karr star (star_star)))
codeT =   TyCon Ox (lv 1) "Code" (poly star_star)
ioT =     TyCon Ox (lv 1) "IO" (poly star_star)
ptrT =    TyCon Ox (lv 1) "Ptr" (poly star_star)
arrowT =  TyCon Ox (lv 1) "(->)" (poly (karr star (star_star)))
eqT =     TyCon Ox (lv 1) "Equal" kind4Eq
hiddenT = TyCon Ox (lv 1) "Hidden" kind4Hidden
chrSeqT = TyCon Ox (lv 1) "ChrSeq" (poly star)
floatT =  TyCon Ox (lv 1) "Float" (poly star)
bindT =   TyCon Ox (lv 1) "Bind" (poly (karr star (star_star)))
stringT = TyApp        listT charT
propT =   TyCon Ox (lv 1) "Prop" (poly star1)
natT =    TyCon Ox (lv 1) "Nat" (poly star1)
notEqT =  TyCon Ox (lv 1) "(!=)" notEqKind

declare (x@(TyCon _ _ name poly)) = (name,x,poly)

-- kind Tag = %name | %age | ... | for all legal symbols
-- data Label t = %name where t=%name | %age where t = %age | ...
tagT    = TyCon Ox (lv 2) "Tag" (poly star1)
labelT  = TyCon Ox (lv 1) "Label" (poly (karr (MK tagT) star))
tagKind = (K(simpleSigma tagT))

-- kind HasType = Has Tag *0
hasTypeT = TyCon Ox (lv 2) "HasType" (poly star1)
hasT     = TyCon Ox (lv 2) "Has" (poly ((MK tagT) `karr` (star `karr` (MK hasTypeT))))

-- Row :: *1 ~> *1
-- kind Row x = RCons x (Row x) | RNil
rowT     = TyCon Ox (lv 2) "Row" (poly (karr star1 star1))

-- RCons :: (forall (k:*1) . k ~> (Row k) ~> Row k)  = RCons
rConsT   = TyCon Ox (lv 1) "RCons" (poly1 star1 f)
           where f k = k `karr` (trow k `karr` trow k)
-- RNil :: (forall (k:*1) . Row k)
rNilT    = TyCon Ox (lv 1) "RNil" (poly1 star1 (\ k -> trow k))


readName mess ([],loc,exts) s = failM 1 [Ds (mess++" unknown type: "++s++", at "),Ds (show loc)]
readName mess ((x,tau,k):xs,loc,exts) s = if s==x then return tau else readName mess (xs,loc,exts) s

kind4Hidden :: PolyKind -- Hidden :: (forall (k:*1) . (k -> *0) -> *0)
kind4Hidden = K(Forall (Cons (star1,All) (bind name1 (Nil ([],ty)))))
   where k = TyVar name1 star1
         ty = Rtau((k `Karr` (Star LvZero)) `Karr` (Star LvZero))

kind4Eq :: PolyKind -- Eq :: (forall (k:*1) . k -> k -> *0)
kind4Eq = K(Forall (Cons (star1,All) (bind name1 (Nil ([],ty)))))
   where k = TyVar name1 star1
         ty = Rtau(k `Karr` (k `Karr` (Star LvZero)))

notEqKind = kind4Eq

kind4Atom :: PolyKind -- Atom :: forall k: *1) . k -> *
kind4Atom = K(Forall (Cons (star1,All) (bind name1 (Nil ([],ty)))))
   where k = TyVar name1 star1
         ty = Rtau(k `Karr` (Star LvZero))


runType = Forall (Cons (star,All)
           (bind name1 (Nil ([],arrow (Forall (Nil ([],tcode a))) a))))
   where a = (Rtau(TyVar name1 star))

liftType = Forall (Cons (star,All)
           (bind name1 (Nil ([],arrow (Forall (Nil ([],a))) (tcode a)))))
   where a = (Rtau(TyVar name1 star))

tequal x y = TyFun infixEqName equalKind [x,y]
tarr x y = applyT [arrowT, x, y]
tlist x = TyApp listT x
tmaybe x = TyApp maybeT x
tmonad x = TyApp monadT x
tpair x y = TyApp (TyApp pairT x) y
tsum x y = TyApp (TyApp sumT x) y
--tcode x = TyApp codeT x
tcode (Rtau x) = Rtau(TyApp codeT x)
tstring = tlist charT
tio x = TyApp ioT x
tptr x = TyApp ptrT x
teq x y = TyApp (TyApp eqT x) y
thidden x = TyApp hiddenT x
tlabel x = TyApp labelT x
ttag s = (TyCon Ox (lv 2) (s) tagKind)
trow (MK x) = MK(TyApp rowT x)



tprods [t] = t
tprods (x:xs) = tpair x (tprods xs)

unPair :: Tau -> [Tau]
unPair (TyApp (TyApp (TyCon _ level_ "(,)" k) x) y) = x:(unPair y)
unPair y = [y]

rK :: Rho -> PolyKind
rK rho = K(Forall (Nil ([],rho)))

tK :: Tau -> PolyKind
tK tau = rK(Rtau tau)

-- given m, produce : (m a -> (a -> m b) -> m b)
bindtype :: TyCh m => Tau -> m Sigma
bindtype m =
   do { av <- fresh; bv <- fresh
      ; let a = TyVar av star
            b = TyVar bv star
      ; return(Forall
        (Cons (star,All) (bind av (Cons (star,All) (bind bv
              (Nil ([],Rtau ((TyApp m a) `tarr`
                          ((a `tarr` (TyApp m b)) `tarr`
                           (TyApp m b)))))))))) }
-- simpler but probably much slower
-- bindtype m = toSigma env (pt "forall a b . m a -> (a -> m b) -> m b")
--   where env = [("m",m,poly star_star)]

failtype :: TyCh m => Tau -> m Sigma
failtype m =
    do { av <- fresh;
      ; let a = TyVar av star
      ; return(Forall
        (Cons (star,All)
              (bind av (Nil ([],Rtau (tstring `tarr` (TyApp m a)))))))
      }

-- Eq :: (forall (k:*1) (u:k) (v:k) . (u = v) => Eq u v)
sigma4Eq = Forall (Cons (star1,All) (bind kname
                  (Cons (k,All) (bind uname
                  (Cons (k,All) (bind vname (Nil (eqns,Rtau eqty))))))))
   where kname = name1
         uname = name2
         vname = name3
         star1 = MK (Star (LvSucc LvZero))
         k = MK(TyVar kname star1)
         u = TyVar uname k
         v = TyVar vname k
         eqns = [Equality u v]
         eqty = TyApp (TyApp eqT u) v


-- Hide :: (forall (k:*1) (f:k -> *0) (u':k) . (f u) -> Hidden f)
sigma4Hide =
    Forall (Cons (star1,All) (bind kname
           (Cons (MK k `karr` star,All) (bind fname
           (Cons (MK k,Ex) (bind uname
           (Nil ([],Rtau((TyApp f u) `tarr` (thidden f))))))))))
 where kname = name1
       fname = name2
       uname = name3
       k = TyVar kname star1
       f = TyVar fname (MK k `karr` star)
       u = TyVar uname (MK k)


s1,s2,s3 :: Tau
s1 = Star (LvSucc LvZero)
s2 = Star (LvSucc (LvSucc LvZero))
s3 = Star (LvSucc (LvSucc (LvSucc LvZero)))
pk = poly star

---------------------------------------------------------
-- instances for the Bind module

instance Swap x => Swap (L x) where
  swaps [] x = x
  swaps cs (Nil x) = Nil(swaps cs x)
  swaps cs (Cons x xs) = Cons (swaps cs x) (swaps cs xs)

instance Swap Quant where
  swaps cs x = x

instance Swap Tau where
  swaps [] x = x
  swaps cs (TyVar n k) = TyVar(swaps cs n) (swaps cs k)
  swaps cs (TyApp x y) = TyApp (swaps cs x) (swaps cs y)
  swaps cs (x@(TyCon _ level_ "(->)" _)) = x  -- Never pull on the kind of (->)
  swaps cs (TyCon sx l s k) = TyCon sx (swaps cs l) s (swaps cs k)
  swaps cs (Star n) = Star n
  swaps cs (Karr x y) = Karr (swaps cs x) (swaps cs y)
  swaps cs (TyFun nm k x) = TyFun (swaps cs nm) (swaps cs k) (swaps cs x)
  swaps cs (TcTv (Tv unq ref k)) = TcTv(Tv unq ref (swaps cs k))
      -- invariant, no type variable will ever bind to something with a TyVar
      -- otherwise we'd have to know how to swap over an IORef
  swaps cs (TySyn nm n fs as t) = TySyn nm n (swaps cs fs) (swaps cs as) (swaps cs t)
  swaps cs (TyEx x) = TyEx (swaps cs x)


instance Swap PolyKind where
  swaps [] x = x
  swaps cs (K r) = K(swaps cs r)

instance Swap Kind where
  swaps [] x = x
  swaps cs (MK t) = MK(swaps cs t)

instance Swap Sigma where
  swaps [] x = x
  swaps cs (Forall b) = Forall (swaps cs b)

instance Swap Rho where
  swaps [] x = x
  swaps cs (Rarrow x y) = arrow (swaps cs x) (swaps cs y)
  swaps cs (Rpair x y) = pair (swaps cs x) (swaps cs y)
  swaps cs (Rsum x y) = rsum (swaps cs x) (swaps cs y)
  swaps cs (Rtau x) = Rtau (swaps cs x)

instance Swap Pred where
  swaps [] x = x
  swaps cs (Equality x y) = Equality (swaps cs x) (swaps cs y)
  swaps cs (Rel ts) = makeRel (swaps cs ts)

-------------------------------------------------------------
-- Typelike instances

fromMaybe x Nothing = x
fromMaybe x (Just w) = w

binaryLift f a b = do { x <- a; y <- b; return(f x y)}

unionP (a,b) (x,y) = (union a x, union b y)

rigid (Rigid _ _ _ ) = True
rigid _ = False

-- TypeLike Tau
instance TyCh m => TypeLike m Tau where
  sub env@(ns,vs,cs,ls) x = do { y <- prune x; f y}
    where f (TyVar nm k) =
            do { k2 <- sub env k
               ; return(fromMaybe (TyVar nm k2) (lookup nm ns))}
          f (TyApp x y) =
            do { x1 <- (sub env x)
               ; y1 <- (sub env y)
               ; return(TyApp x1 y1)}
          f (TyCon sx l s k) =
            do { k2 <- sub env k
               ; l2 <- sub env l
               ; let x = (fromMaybe (TyCon sx l2 s k2) (lookup s cs))
               ; return x}
          f (Star n) = do { level <- sub env n; return(Star level)}
          f (Karr x y) =  binaryLift Karr (sub env x) (sub env y)
          f (TyFun nm k x) = do { y <- sub env x; k' <- sub env k; return(TyFun nm k' y) }
          f (TcTv (x@(Tv uniq flav k))) =
            do { case lookup x vs of
                  Just tau -> return tau
                  Nothing -> do { k2 <- sub env k; return(TcTv(Tv uniq flav k2))}
               }
          f (TySyn nm n fs as t) =
             do { as2 <- sub env as; t2 <- sub env t;
                ; fs2 <- mapM g fs; return(TySyn nm n fs2 as2 t2)}
           where g (nm,k) = do { k2 <- sub env k; return(nm,k2)}
          f (TyEx x) = do { w <- sub env x; return(TyEx w)}

  zonk x = do { y <- prune x; f y}
    where f (TyVar nm k) = do { k2 <- zonk k; return(TyVar nm k2)}
          f (TyApp x y) =  binaryLift TyApp (zonk x) (zonk y)
          f (TyCon sx l s k) =  do { k2 <- zonk k; l2 <- zonk l; return(TyCon sx l2 s k2) }
          f (Star n) = do { m <- zonk n; return(Star m)}
          f (Karr x y) =  binaryLift Karr (zonk x) (zonk y)
          f (TyFun nm k x) =  do { y <- zonk x; k' <- zonk k; return(TyFun nm k' y) }
          f (TcTv (Tv un flav k)) = do { k2 <- zonk k; return(TcTv(Tv un flav k2))}
          f (TySyn nm n fs as t) =
             do { as2 <- zonk as; t2 <- zonk t
                ; fs2 <- mapM g fs; return(TySyn nm n fs2 as2 t2)}
             where g (nm,k) = do { k2 <- zonk k; return(nm,k2)}
          f (TyEx x) = do { w <- zonk x; return(TyEx w)}

  get_tvs x = do { y <- prune x; f y}
    where f (TcTv (x@(Tv unq _ k))) = binaryLift unionP (get_tvs k) (return ([x],[]))
          f (TyApp x y) = binaryLift unionP (get_tvs x) (get_tvs y)
          f (Karr x y) = binaryLift unionP (get_tvs x) (get_tvs y)
          f (TyFun nm k x) = binaryLift unionP (get_tvs k) (get_tvs x)
          f (Star n) = get_tvs n
          f (TyCon _ level_ s k) = get_tvs k
          f (TyVar nm k) = get_tvs k
          f (TySyn nm n fs as t) = binaryLift unionP (get_tvs as)
                                   (binaryLift unionP (get_tvs (map snd fs)) (get_tvs t))
          f (TyEx x) = get_tvs x

  --nf x = nfTau x

subT env t = sub ([],env,[],[]) t

-- TypeLike Rho
instance TyCh m => TypeLike m Rho where
  sub env (Rarrow x y) = binaryLift arrow (sub env x) (sub env y)
  sub env (Rpair x y)  = binaryLift pair (sub env x) (sub env y)
  sub env (Rsum x y)   = binaryLift rsum (sub env x) (sub env y)
  sub env (Rtau x) = do { w <- sub env x; return(Rtau w)}

  zonk (Rarrow x y) = binaryLift arrow (zonk x) (zonk y)
  zonk (Rpair x y) = binaryLift pair (zonk x) (zonk y)
  zonk (Rsum x y) = binaryLift rsum (zonk x) (zonk y)
  zonk (Rtau x) = do { w <- zonk x; return(Rtau w)}

  get_tvs (Rarrow x y) = binaryLift unionP (get_tvs x) (get_tvs y)
  get_tvs (Rsum x y) = binaryLift unionP (get_tvs x) (get_tvs y)
  get_tvs (Rpair x y) = binaryLift unionP (get_tvs x) (get_tvs y)
  get_tvs (Rtau x) = get_tvs x

  --nf x = nfRho x

-- TypeLike Sigma
instance  TyCh m => TypeLike m Sigma where
  sub env (Forall xs) = do { w <- sub env xs; return(Forall w)}
  zonk (Forall b) = do { w <- zonk b; return(Forall w)}
  get_tvs (Forall b) = get_tvs b
  --nf x = nfSigma x

-- TypeLike PolyKind
instance  TyCh m => TypeLike m PolyKind where
  sub env (K r) = do { r' <- sub env r; return(K r')}
  zonk (K r) = do { r' <- zonk r; return(K r')}
  get_tvs (K r) = get_tvs r
  --nf (K x) = do { z <- nfSigma x; return(K z) }

-- TypeLike Kind
instance  TyCh m => TypeLike m Kind where
  sub env (MK r) = do { r' <- sub env r; return(MK r')}
  zonk (MK r) = do { r' <- zonk r; return(MK r')}
  get_tvs (MK r) = get_tvs r
  --nf (MK x) = do { z <- nfTau x; return(MK z) }

-- TypeLike Equations
instance TyCh m => TypeLike m Pred where
  sub env (Equality x y) = do { a <- sub env x; b <- sub env y; return(Equality a b)}
  sub env (Rel ts) = do {ys <- sub env ts; return(makeRel ys)}
  zonk (Equality x y) = do { a <- zonk x; b <- zonk y; return(Equality a b)}
  zonk (Rel ts) = do {ys <- zonk ts; return(makeRel ys)}
  get_tvs (Equality x y) = binaryLift unionP (get_tvs x) (get_tvs y)
  get_tvs (Rel ts) = (get_tvs ts)
  --nf x = tevalEq [] x
  --nf (Equality x y) = binaryLift Equality (nfTau x) (nfTau y)
  --nf (Rel ts) = do { ys <- nf ts; return(makeRel ys)}


--- Helper functions for unwinding the (L Rho) objects in Forall

unwind :: (Swap (L a), Fresh m) => L a -> m (ForAllArgs,a)
unwind (Nil t) = return ([],t)
unwind (Cons (k,q) b) =
   do { (x,rest) <- unbind b
      ; (xs,t) <- unwind rest
      ; return((x,k,q):xs,t)
      }

windup :: Swap (L a) => ForAllArgs -> a -> L a
windup [] t = Nil t
windup ((x,k,q):xs) t = Cons (k,q) (bind x (windup xs t))

addToL :: Swap (L a) => ForAllArgs -> L a -> L a
addToL [] ys = ys
addToL ((nm,k,q):xs) ys = Cons (k,q) (bind nm (addToL xs ys))

-----------------------------------------------
-- structures of TypeLike things are TypeLike

-- TypeLike L
instance (Swap r,TypeLike m r,TyCh m) => TypeLike m (L r) where
  sub env (Nil x) = do { w <- sub env x; return(Nil w)}
  sub env (Cons (k,q) b) =
      do { (nm,r) <- unbind b
         ; k' <- sub env k
         ; r' <- sub env r
         ; return(Cons (k',q) (bind nm r'))}

  zonk (Nil x) = do { w <- zonk x; return(Nil w)}
  zonk (Cons (k,q) b) =
      do { (nm,r) <- unbind b
         ; k' <- zonk k
         ; r' <- zonk r
         ; return(Cons (k',q) (bind nm r'))}
  get_tvs (Nil b) =  get_tvs b
  get_tvs (Cons (k,q) b) =
      do { (nm,r) <- unbind b; binaryLift unionP (get_tvs k) (get_tvs r) }
  --nf xs = error "No Normal form for (TypeLike m (L r)) instance"


instance TypeLike m t => TypeLike m (Maybe t) where
  sub env (Just t) = do { x <- sub env t; return(Just t)}
  sub env (Nothing) = return(Nothing)
  zonk (Just t) = do { x <- zonk t; return(Just t)}
  zonk (Nothing) = return(Nothing)
  get_tvs (Just t) = get_tvs t
  get_tvs (Nothing) = return([],[])
  --nf (Just t) = do { x <- nf t; return(Just t)}
  --nf (Nothing) = return(Nothing)


-- Infer objects are sometime populated with 'doNotPullOnMe'
-- so we never want to pull on them, unless we know
-- they have been over written.


instance TypeLike m t => TypeLike m (Expected t) where
  sub env (Check t) = do { x <- sub env t; return(Check t)}
  sub env (Infer r) = return(Infer r)
  zonk (Check t) = do { x <- zonk t; return(Check t)}
  zonk (Infer r) = return(Infer r)
  get_tvs (Check t) = get_tvs t
  get_tvs (Infer r) = return([],[])
  --nf (Check t) = do { x <- nf t; return(Check t)}
  --nf (Infer r) = return(Infer r)

-- TypeLike []  i.e. Lists
instance TypeLike m t => TypeLike m [t] where
  sub env ts = mapM (sub env) ts
  zonk ts = mapM zonk ts
  get_tvs ts =
    do { vss <- mapM get_tvs ts
       ; let (ts,ls) = unzip vss
       ; return (nub (concat ts), nub (concat ls)) }
  --nf x = mapM nf x

-- TypeLike (,)  i.e. Pairs
instance (TypeLike m a,TypeLike m b) => TypeLike m (a,b) where
  sub env (x,y) = do { a <- sub env x; b <- sub env y; return(a,b)}
  zonk (x,y) = do { a <- zonk x; b <- zonk y; return(a,b)}
  get_tvs (x,y) = binaryLift unionP (get_tvs x) (get_tvs y)
  --nf (x,y) = binaryLift (,) (nf x) (nf y)

-- TypeLike (,,)  i.e. Triples
instance (TypeLike m a,TypeLike m b,TypeLike m c) => TypeLike m (a,b,c) where
  sub env (x,y,z) = do { a <- sub env x; b <- sub env y; c <- sub env z; return(a,b,c)}
  zonk (x,y,z) = do { a <- zonk x; b <- zonk y; c <- zonk z; return(a,b,c)}
  get_tvs (x,y,z) = binaryLift unionP (binaryLift unionP (get_tvs x) (get_tvs y)) (get_tvs z)
  --nf (x,y,z) = do { a<- nf x; b <- nf y; c <- nf z; return(a,b,c)}


instance TyCh m => TypeLike m TcTv where
  sub env x = return x
  zonk x = return x
  get_tvs x = return ([],[])
  --nf x = return x

instance TyCh m => TypeLike m Char where
  sub env ts = return ts
  zonk ts = return ts
  get_tvs ts = return ([],[])
  --nf x = return x

-----------------------------------------------
-- Quantify instances

instance TyCh m => Quantify m Tau where
  for_all xs r = return(Forall(windup xs ([],Rtau r)))

instance TyCh m => Quantify m Rho where
  for_all xs t = return(Forall(windup xs ([],t)))

instance TyCh m => Quantify m Sigma where
  for_all xs (Forall ys)  = return(Forall (addToL xs ys))

instance TyCh m => Quantify m Kind where
  for_all xs (MK r) = for_all xs r

instance TyCh m => Quantify m PolyKind where
  for_all xs (K s) = for_all xs s

instance TyCh m => Quantify m ([Pred],Sigma) where
  for_all xs (eqn,Forall ys) =
    do { (zs,(eqn2,rho)) <- unwind ys
       ; return(Forall (windup (xs++zs) (eqn++eqn2,rho)))}

instance TyCh m => Quantify m ([Pred],Rho) where
  for_all xs r = return(Forall (windup xs r))

instance TyCh m => Quantify m ([Pred],Tau) where
  for_all xs (eqs,tau) = return(Forall (windup xs (eqs,Rtau tau)))


---------------------------------------------------------------------
-- unify tries to unify to Tau types, This enforces that you can't
-- unify embedded Foralls, or TyVars which only occur inside Foralls

prune :: TyCh m => Tau -> m Tau
-- the new style does the Rigid translation in lookUpVar,
-- applying theta if the binding is Rigid
-- prune (typ @ (TcTv (v @ (Tv uniq (Rigid _ _ _) k)))) = pruneV typ v
-- prune (typ @ (TcTv (v @ (Tv uniq (Skol _) k)))) = pruneV typ v
prune (typ @ (TcTv (Tv uniq (Flexi ref) k))) =
  do { maybet <- readRef ref
     ; case maybet of
         Nothing -> return typ
         Just t -> do{t2 <- prune t; writeRef ref (Just t2); return t2}}
prune t = return t

pruneV typ v =
  do { theta <- getBindings
     ; case lookup v theta of
         Just new -> if typ==new then return new else prune new
         Nothing -> return typ }


unify :: TyCh m => Tau -> Tau -> m ()
unify x y =
     do { x1 <- prune x; y1 <- prune y
        --; outputString("Unifying "++show x1++" =?= "++show y1)
        ; f x1 y1
        }
  where f (t1@(TyVar n k1)) t2 =
          matchErr "TyVar in unify, this should never happen" t1 t2
        f t1 (t2@(TyVar n k1)) =
          matchErr "TyVar in unify, this should never happen" t2 t1
        f (TyApp x y) (TyApp a b) = do { unify x a; unify y b }
        f (x@(TyCon sx l s _)) (y@(TyCon tx k t _)) =
           do { unifyLevel l k
              ; if s==t then return () else matchErr "different constants" x y }
        f (x@(Star n)) (y@(Star m)) = unifyLevel n m
           -- if n==m then return () else matchErr "different level" x y
        f (Karr x y) (Karr a b) = do { unify x a; unify y b }
        f (TySyn nm1 n1 f1 a1 t1) t2 = unify t1 t2
        f t1 (TySyn nm2 n2 f2 a2 t2) = unify t1 t2
        f (TcTv x) t = unifyVar x t
        f t (TcTv x) = unifyVar x t
        f (x@(TyFun nm k _)) y = emit x y
        f y (x@(TyFun nm k _)) = emit x y

        -- handled by unifyVar
        --f (x@(TcTv(Tv u (Rigid _ _ _) k))) y = emit x y
        --f y (x@(TcTv(Tv u (Rigid _ _ _) k))) = emit y x
        f (TyEx x) (TyEx y) = unifyEx x y
        f s t = matchErr "\nDifferent types" s t


emit x y = do { a <- zonk x; b <- zonk y
              ; verbose <- show_emit
              ; whenM verbose [Ds "\nGenerating predicate\n  ",Dd a, Ds " =?= ",dn b]
              ; injectA " emitting " [equalRel a b]}
equalRel x y = Equality x y

unifyEx x y =
 do { (tripsX,(eqn1,x1)) <- unwind x
    ; (tripsY,(eqn2,y1)) <- unwind y
    ; let pair (nm1,k1,q1) (nm2,k2,q2) = (nm1,nm2)
          cs = zipWith pair tripsX tripsY
          new (nm1,k1,q1) = do { x <- newSkolTyVar (show nm1) k1; return(nm1,TcTv x)}
    ; sub <- mapM new tripsX
    ; x2 <- subst sub x1
    ; y2 <- subst sub (swaps cs y1)
    ; pred1 <- substPred sub eqn1
    ; pred2 <- substPred sub (swaps cs eqn2)
    ; if predsEq pred1 pred2
         then unify x2 y2
         else failM 1 [Ds "Exist types have unequal predicates:\n  "
                      ,Dd eqn1,Ds " =/= ",Dd eqn2]
    }

predsEq xs ys = (all (`elem` xs) ys) && (all (`elem` ys) xs)

unifyVar (x@(Tv u1 r1 k1)) (t@(TcTv (Tv u2 r2 k2))) | u1==u2 = return ()
-- Always bind newer vars to older ones, this way
-- makes the pretty printing work better
unifyVar (x@(Tv u1 (Flexi _) _)) (TcTv(y@(Tv u2 (Flexi _) _)))
  | u1 < u2 = unifyVar y (TcTv x)
unifyVar (x@(Tv u1 (Flexi r1) (MK k))) t =
  do { (vs,level_) <- get_tvs t
     ; t2 <- zonk t
     ; when (any (==x) vs) (matchErr "Occurs check" (TcTv x) t2)
     ; (new_t) <- handleM 1 (check t k) (kinderr t k u1)
     ; writeRef r1 (Just t2)
     ; return ()
     }
unifyVar (x@(Tv _ (Rigid _ _ _) _)) (TcTv v@(Tv _ (Flexi _) _)) = unifyVar v (TcTv x)
unifyVar (x@(Tv _ (Skol s) _))      (TcTv v@(Tv u2 r2 k2))      = unifyVar v (TcTv x)
unifyVar (x@(Tv _ (Rigid _ _ _) _)) (y@(TcTv v@(Tv _ (Rigid _ _ _) _))) = emit (TcTv x) y
unifyVar v (x@(TyFun nm k _)) = emit (TcTv v) x
unifyVar v t = matchErr "(V) different types" (TcTv v) t


matchErr s t1 t2 = failM 0
   [Ds (s++"\n   "),Dd t1,Ds "   !=   ",Dd t2,Ds "\n",Ds (show(t1,t2))]

kinderr t k u1 s =
   failM 0
    [Ds "Type: ",Dd t,Ds "\ndoes not have kind: ",Dd k,Ds (s++"\n var = "),Dd u1]


-----------------------------------------
-- Force a Rho type to have an Rarrow shape, a Pair shape, a Sum shape

unifyFun :: TyCh m => Rho -> m (Sigma,Rho)
unifyFun (Rarrow x y) = return (x,y)
unifyFun (Rtau (TyApp (TyApp z@(TyCon sx level_ "(->)" doNotPullThis) x) y)) =
   return(Forall (Nil ([],Rtau x)) ,Rtau y)
unifyFun (Rtau x) =
   do { a <- newTau star
      ; b <- newTau star
      ; unify x (tarr a b)
      ; a1 <- zonk a
      ; b1 <- zonk b
      ; return (simpleSigma a1,Rtau b1) }
unifyFun x = failM 0 [Ds "Expected an function type: ",Dd x]


unifyCode :: TyCh a => Expected Rho -> a Rho
unifyCode (Check (Rtau (TyApp (TyCon sx level_ "Code" k) a))) = return (Rtau a)
unifyCode expected =
  do { a <- newRho star; zap a (tcode a) expected }

sigmaTwo :: TyCh m => (Tau -> Tau -> Tau) -> Sigma -> m(Sigma,Sigma)
sigmaTwo mkTwo (Forall xs) =
   do { (tvs,eqs,b) <- unBindWithL newflexi xs
      ; (p1,p2) <- case b of
          Rpair x y -> return(x,y)
          Rtau x -> do { a <- newTau star; b <- newTau star
                       ; unify x (mkTwo a b);
                       ; z1 <- zonk a; z2 <- zonk b
                       ; return(simpleSigma z1,simpleSigma z2) }
      ; (mapping,newbinders1,body1) <- subFreshNames tvs [] (eqs,p1)
      ; (_,newbinders2,body2) <- subFreshNames tvs mapping (eqs,p2)
      ; sigma1 <- for_all newbinders1 body1
      ; sigma2 <- for_all newbinders2 body2
      ; return(sigma1,sigma2) }

sigmaPair :: TyCh m => Sigma -> m (Sigma,Sigma)
sigmaPair t = do { t2 <- zonk t; sigmaP t2}
  where sigmaP (Forall (Nil ([],Rpair x y))) = return (x,x)
        sigmaP x = sigmaTwo tpair x

sigmaSum :: TyCh m => Sigma -> m (Sigma,Sigma)
sigmaSum t = do { t2 <- zonk t; sigmaS t2}
  where sigmaS (Forall (Nil ([],Rsum x y))) = return (x,x)
        sigmaS x = sigmaTwo tsum x

expecting ::
  TyCh m => String -> (Tau -> Tau -> Tau) -> Expected Rho -> m (Rho,Rho)
expecting shape f expect =
  do { a <- newTau star; b <- newTau star
     ; case expect of
         Check (Rtau p) -> unify p (f a b)
         Infer ref -> do { a <- zonk (Rtau (f a b)); writeRef ref a }
         Check other -> failM 0 [Ds "Expecting a ",Dd shape,Ds ": ",Dd other]
     ; t1 <- zonk a
     ; t2 <- zonk b
     ; return(Rtau t1,Rtau t2) }

---------------------------------------------------------------------
-- create new fresh variables and types

newFlexiTyVar :: TyCh m => Kind -> m TcTv
newFlexiTyVar k =
  do { n <- nextInteger ;
     ; r <- newRef Nothing ;
     ; return (Tv n (Flexi r) k) }

newRigidTyVar :: TyCh m => Quant -> Loc -> String -> Kind -> m TcTv
newRigidTyVar q loc s k =
  do { n <- nextInteger; return(Tv n (Rigid q loc s) k) }

newSkolTyVar :: TyCh m => String -> Kind -> m TcTv
newSkolTyVar s k =
  do { n <- nextInteger; return(Tv n (Skol s) k) }

-- every var a Skolem var
skolTy :: TyCh m => Sigma -> m ([TcTv],[Pred],Rho)
skolTy sigma = unBindWith newSkolem sigma

-- "new" from "unBindWithL" will be one of these three functions
newflexi       nam quant k = do { v <- newFlexiTyVar k; return(TcTv v)}
newSkolem      nam quant k = do { v <- newSkolTyVar (show nam) k; return(TcTv v)}
newRigid loc s nam quant k = do { v <- newRigidTyVar quant loc s k; return(TcTv v) }


newTau k = do { v <- newFlexiTyVar k; return (TcTv v)}
newRho k = do { v <- newTau k; return(Rtau v)}
newSigma k = do { v <- newTau k; return (simpleSigma v)}

testflex n = unsafePerformIO $
  do { r <- newIORef Nothing
     ; return(Tv n (Flexi r) star) }



newKind k = do { v <- newTau k; return (MK v) }

simpleSigma tau = Forall (Nil ([],Rtau tau))
mediumSigma eqs tau = Forall (Nil (eqs,Rtau tau))

newByLevel :: TyCh m => Int -> m Tau
newByLevel n = help n (MK (Star (lv n)))
  where help 0 k = newTau k
        help n k = do { kn <- newTau k; help (n-1) (MK kn) }

--------------------------------------------------------------------
-- Instantiation. Turn a Sigma into a Rho by instantiating its vars,


-- every var a Flexi var, and apply the substitution implied by the equations
instanTy :: TyCh m => Sigma -> m([Pred],Rho)
instanTy (Forall s) = do { (vs,ps,r) <- instanL s; return(ps,r) }

-- instanL :: (Show b,TypeLike m b, Swap b) => L ([Pred],b) -> m ([TcTv],[Pred],b)
instanL s =
  do { (vs,eqns,r) <- unBindWithL newflexi s
     ; (unifyPred,preds2,r2) <- normalizeEqn eqns r
     ; (u,p,r) <- zonk (unifyPred,preds2,r2)
     ; return(vs,preds2,r2) }

-------------------------------------------------------------------------

split3 :: [Pred] -> ([Tau],[(Tau,Tau)],[(TcTv,Tau)])
split3 ((Equality (TcTv x) y):zs) = (ps,xs,(x,y):bs) where (ps,xs,bs) = split3 zs
split3 ((Equality y (TcTv x)):zs) = (ps,xs,(x,y):bs) where (ps,xs,bs) = split3 zs
split3 ((Equality x y):zs) = (ps,(x,y):xs,bs) where (ps,xs,bs) = split3 zs
split3 (Rel t : zs) = (t:ps,xs,bs) where (ps,xs,bs) = split3 zs
split3 [] = ([],[],[])


-- When type checking patterns, we try and see if the patterns
-- have consistent substitutions, we need to collect the
-- Equalities that don't mention skolem vars or type fnctions
-- to produce a substitution.
-- Split out (x=y) except if x = skol or y={plus y z} a TyFun

splitU [] = ([],[])
splitU ((p@(Equality (x@(TyFun _ _ _)) y)):zs) =
       ((Equality y x):ps,bs) where (ps,bs) = splitU zs
splitU ((p@(Equality x (y@(TyFun _ _ _)))):zs) =
       ((Equality y x):ps,bs) where (ps,bs) = splitU zs
splitU ((p@(Equality (TcTv (Tv un (Skol _) k)) y)):zs) = (p:ps,bs) where (ps,bs) = splitU zs
splitU ((Equality (TcTv x) y):zs) = (ps,(x,y):bs) where (ps,bs) = splitU zs
splitU ((Equality y (TcTv x)):zs) = (ps,(x,y):bs) where (ps,bs) = splitU zs
splitU (p:zs) = (p:ps,bs) where (ps,bs) = splitU zs



--------------------------------------------------------------------

-- each var according to its Quant, either Rigid or Flexi
instanPatConstr :: TyCh a => Quant -> Loc -> [Char] -> Sigma -> a ([TcTv],[Pred],Rho)
instanPatConstr q loc s ty =
   do { (vs,eqs,r) <- unBindWith new ty
      ; return(filter p vs,eqs,r) }
   where new nam Ex k = newRigid loc s nam Ex k
         new nam All k = newflexi nam All k
         p (Tv  uniq (Flexi _) k) = False
         p _ = True

unBindWith :: (TyCh m) => (Name -> Quant -> Kind -> m Tau) -> Sigma -> m ([TcTv],[Pred],Rho)
unBindWith new (Forall b) = unBindWithL new b

unBindWithL:: (TypeLike m c, Swap c) => (Name -> Quant -> Kind -> m Tau) -> L ([Pred],c) -> m ([TcTv],[Pred],c)
unBindWithL new b = f b []
 where unTcTv (name,TcTv v) = v
       f (Nil (zs,r)) env =
          do { r' <- subst env r
             ; zs2 <- subst env zs
             ; return(map unTcTv env,zs2,r')}
       f (Cons (k,quant) b) env =
          do { (n,xs) <- unbind b
             ; k2 <- subst env k
             ; var <- new n quant k2
             ; env2 <- (comp (n,var) env)
             ; f xs env2 }
       extend (n,var) (name,tau) = do { tau2 <- subst [(n,var)] tau; return(name,tau2)}
       comp (n,var) xs = do { ys <- mapM (extend (n,var)) xs ; return(ys ++ [(n,var)])}



--------------------------------


----------------------------------------------------------------------------
-- The opposite of instantiation (Sigma -> Rho) is quantification
-- (Rho -> Sigma). But in general many other things can be quantified other
-- than Rho. Quantification abstracts over each free TcTv as All Quant
-- variables. Ex Quant vars in Forall's come only from Existential types
-- in data defs. Eg.     data Dyn = exists t . Dyn (Rep t) t
-- so quantify  will never produce one.

quantify :: (TypeLike m t,Quantify m t,Display t Z,Sht t) => [TcTv] -> t -> m Sigma
quantify tvs ty =
  do { (_,newbinders,ty2) <- subFreshNames tvs [] ty
     ; for_all newbinders ty2
     }

subFreshNames :: (TyCh m,TypeLike m t,Display t Z,Sht t)
  => [TcTv] -> [(TcTv,Tau)] -> t -> m( [(TcTv,Tau)],[(Name,Kind,Quant)],t)
subFreshNames [] env ty =
   do { w <- sub ([],env,[],[]) ty -- TODO LEVEL
     ; return(env,[],w) }
subFreshNames (v@(Tv unq (Flexi ref) k):xs) env ty =
   do { name <- fresh
      ; k2 <- sub ([],env,[],[]) k -- TODO LEVEL
      ; (env2,ys,w) <- subFreshNames xs ((v,TyVar name k2):env) ty
      ; return(env2,(name,k2,All):ys,w)
      }
subFreshNames (v:xs) env ty = subFreshNames xs env ty -- ignore non-flexi vars

generalize :: (TypeLike m t,Quantify m t,Display t Z,Sht t) => t -> m Sigma
generalize rho =
  do { rho2 <- zonk rho   -- We used to Normalize but this caused problems
     ; (rvars,level_) <- get_tvs rho2 -- TODO LEVEL
     ; evars <- envTvs
     ; let generic = filter (not . (`elem` evars)) rvars
     ; sig <- quantify generic rho2
     ; zonk sig
     }


-------------------------------------------------------------
-- Typable instances

---------------------------------------------------------------------
-- If a term is Typable as a Rho,
-- one can derive Typabilty as a Sigma for Free!
-- Typability for Tau and Rho depends on the semantics of Term
-- so it is usually defined in the file that defines terms.

polyP (Forall (Cons _ _)) = True
polyP (Forall (Nil _)) = False
-- polyP x = False

--------------------------------------------------------
-- When we instantiate a Forall type, it might mention
-- some Equalities. Some of these are just binders, e.g. "a" below:
-- Cons :: forall (a:Nat) (b:Nat) . a=#(1+b) => Bit -> Bvec b -> Bvec a
-- we want to build a substitution out of these and collect
-- the others predicates for solving by narrowing.

splitSkol :: [TcTv] -> [Pred] -> ([Pred],[(TcTv,Tau)])
splitSkol vs [] = ([],[])
splitSkol vs ((Equality (TcTv x) y):zs) | elem x vs = (ps,(x,y):bs)
       where (ps,bs) = splitSkol vs zs
splitSkol vs ((Equality y (TcTv x)):zs) | elem x vs = (ps,(x,y):bs)
       where (ps,bs) = splitSkol vs zs
splitSkol vs (p:zs) = (p:ps,bs) where (ps,bs) = splitSkol vs zs

-- Typable Sigma
instance (Show term, Exhibit (DispInfo Z) term,Typable m term Rho
         ,Accumulates m Pred) => Typable m term Sigma where

  -- if the Sigma isn't really a Sigma then don't bother
  check expr (Forall(Nil([],rho))) = check expr rho
  check expr exp_ty
    = do { (skol_tvs, assump, rho) <- skolTy exp_ty
         ; let (preds,bindings) = splitSkol skol_tvs assump
         ; rho1 <- subT bindings rho
         ; (preds2,unifier) <- solveSomeEqs ("9."++show expr,rho1) preds
         ; rho2 <-  subT unifier rho
         ; let verbose = False
         ; whenM verbose
                  [Ds ("\n(Check term Sigma) The term is: "++ show expr)
                  ,Ds "\nThe type is: ",Dd exp_ty
                  ,Ds "\nskolem is: ",Dd rho
                  ,Ds "\nassump: = ",Dd assump,Ds (show assump)
                  ,Ds "\nSkolem vars are: ",Dl skol_tvs ","
                  ,dv "rho2" rho2]
         ; rho3 <- sub ([],unifier,[],[]) rho2
         ; (s,need::[Pred]) <-  extractAccum (assume preds2 unifier (check expr rho2))
         ; whenM verbose
                [Ds ("\n(check term Sigma) ("++show expr++"), need = "),Dl need ", "
                 ,dv ", rho3" rho3,dv ", unifier" unifier]
         ; (passOn,_) <- solveHP (show expr,rho2) assump need
         ; (tvs2, level_) <- get_tvs exp_ty -- TODO LEVEL
         ; env_tvs <- envTvs
         ; let esc_tvs = env_tvs ++ tvs2
               bad_tvs = filter (`elem` esc_tvs) skol_tvs
         ; case bad_tvs of
              [] -> return ()
              zs -> failM 1 [Ds "Type not polymorphic enough",Dl zs ", "]
         ; injectA " in check " passOn
         ; return s }

  -- We're defining, infer :: Typable a Sigma => a -> Tc Sigma
  -- inside we use,  infer :: Typable a Rho => a -> Tc Rho
  infer e
   = do { (exp_ty::Rho,s) <- infer e
        ; (res_tvs, level_) <- get_tvs exp_ty -- TODO LEVEL
        ; env_tvs <- envTvs
        --; let env_tvs = varsFromTriples trips   -- Guaranteed zonked
        ; let forall_tvs = res_tvs \\ env_tvs
        ; t <- quantify forall_tvs exp_ty
        ; return(t,s) }

------------------------------------------------------
-- How to do Kind inference for all 3 forms of types.
-- Tau :: Tau , Rho :: Tau , and Sigma :: Tau
------------------------------------------------------

getTy (Check s) = return s
getTy (Infer ref) = readRef ref


-- Typable Tau
-- first show that each can be infered to have a Tau type.
instance TyCh m => Typable m  Tau Tau where
  tc tau expect = do { -- warnM [Ds "\nCheck ",Dd tau, Ds ":?: ",Dd expect];
                       r <- prune tau;  f r expect }
   where
    f t@(TcTv (Tv u r (MK rho))) expect = mustBe ("type","kind") t rho expect
    f t@(TyCon sx level_ s k) expect = zapPoly t k expect
    f t@(Star n) expect = mustBe ("kind","sort") t (Star (LvSucc n)) expect
    f (Karr x y) expect =
      do { (k :: Tau,x1) <- infer x
         ; y1 <- tc y expect
         ; return(Karr x1 y1) }
    f t@(TyVar n (MK k)) expect = zap t k expect
    f t@(TyFun nm (k@(K sig)) xs) expect =
      do { (preds,rho) <- instanTy sig
         ; when (not(null preds)) (failM 0 [Ds "Type functions can't have constrained kinds: ",Dd sig])
         ; ys <- checkTyFun nm rho xs expect
         ; return(TyFun nm k ys)}
    f t@(TyApp ff x) expect =
      do { (fk,a) <- infer ff
         ; fk2 <- zonk fk
         ; (arg_ty,res_ty) <- unifyKindFun ff fk2
         ; let err mess = failM 2
                [Ds "\nwhile checking the kind of ("
                ,Dd t, Ds ")" {- , Ds (shtt t) -}
                , Ds " we expected (",Dd x
                ,Ds "::  ",Dd arg_ty,Ds ")\nbecause (",Dd ff
                ,Ds ":: ",Dd fk2,Ds (") but "++mess)]
         ; b <- handleM 2 (check x arg_ty) err

         ; morepoly (show t) res_ty expect
         ; return (TyApp a b)}
    f t@(TySyn nm n fs as b) expect =
      do { let g (nm,MK k) t = check t k
         ; sequence (zipWith g fs as)
         ; f b expect }
    f (TyEx xs) expect = do { ys <- tc xs expect; return(TyEx ys) }


-- "infer" and "check" walk over a type infering type information
-- from the structure of the type and information in the type
-- environment. They placing kind annotations
-- at the leaves (in variables), "kindOf" and "kindOfM"
-- walk over an annotated tree and compute the kind of the
-- type. This could be a pure function, except for the
-- possibility of polymorphic TyCon's. Then we need to
-- generate new 'kind variables', so it must be monadic.
-- We supply a pure function "kindOf" but it is inexact.

kindOf :: Tau -> Tau
kindOf (TcTv (Tv u r (MK k))) = k
kindOf (TyCon sx level_ s (K (Forall xs))) =
   case unsafeUnwind xs of
     (vs,(_,Rtau k)) -> k
     (vs,(_,rho)) -> error ("Non Tau in kind of Type constructor: "++show rho)
kindOf (Star n) = (Star (LvSucc n))
kindOf (Karr x y) = kindOf y
kindOf (TyVar n (MK k)) = k
kindOf (TyFun s (K (Forall xs)) ts) =
   case unsafeUnwind xs of
     (vs,(_,Rtau k)) ->  unwind ts k
     (vs,(_,rho)) -> error ("Non Tau in Type function kind: "++show rho)
 where unwind [] k = k
       unwind (x:xs) (Karr a b) = unwind xs b
       unwind _ k = error ("Non (~>) in Type function kind: "++show k)
kindOf (TyApp ff x) =
  case kindOf ff of
    (Karr a b) -> b
    k -> error ("Non (~>) in Type application: "++show k)
kindOf (TySyn nm n fs as b) = kindOf b
kindOf (TyEx xs) =
    case unsafeUnwind xs of
     (vs,(_,k)) -> k

kindOfM :: TyCh m => Tau -> m Tau
kindOfM (TcTv (Tv u r (MK k))) = return k
kindOfM (TyCon sx level_ s (K sigma)) =
  do { info <- instanTy sigma
     ; case info of
       ([],Rtau k) -> return k
       other -> failM 0 [Ds "An illegal kind in a TyCon was found while computing the kind of a type: ",Dd sigma] }
kindOfM (Star n) =  return (Star (LvSucc n))
kindOfM (Karr x y) = kindOfM y
kindOfM (TyVar n (MK k)) = return k
kindOfM (TyFun s (K sigma) ts) =
  do { info <- instanTy sigma
     ; case info of
       ([],Rtau k) -> matchKind k ts
       other -> failM 0 [Ds "An illegal kind in a Type Funtion was found while computing the kind of a type: ",Dd sigma] }
kindOfM (ty@(TyApp ff x)) =
  do { let (f,ts) = rootTau ty []
     ; k <- kindOfM f
     ; matchKind k ts }
kindOfM (TySyn nm n fs as b) = kindOfM b
kindOfM (TyEx xs) = do { (_,_,t) <- instanL xs; kindOfM t}



matchKind (Karr a b) (t:ts) =
  do { k <- kindOfM t
     ; unify a k
     ; matchKind b ts }
matchKind k [] = zonk k

checkTyFun :: TyCh m => String -> Rho -> [Tau] -> Expected Tau -> m [Tau]
checkTyFun nm (Rtau k) [] (Infer ref) = do { a <- zonk k; writeRef ref a; return[] }
checkTyFun nm (Rtau k) [] (Check m) = do { morepoly nm k m; return [] }
checkTyFun nm (Rtau k) (t:ts) expect =
  do { (dom,rng) <- unifyKindFun t k
     ; t2 <- check t dom
     ; ts2 <- checkTyFun nm (Rtau rng) ts expect
     ; return(t2:ts2)
     }
checkTyFun nm rho ts expect = failM 0 [Ds ("Type fun "++nm++" has rho type: "),Dd rho]



------------------------------------------------------------
-- Helper functions for kind inference

unifyKindFun :: TyCh m => Tau -> Tau -> m (Tau,Tau)
unifyKindFun term (TySyn nm n fs as t) = unifyKindFun term t
unifyKindFun term (Karr x y) = return (x,y)
unifyKindFun term x@(TcTv (Tv unq _ k)) =
   do { a <- newTau k
      ; b <- newTau k
      ; unify x (Karr a b)
      ; a1 <- zonk a
      ; b1 <- zonk b
      --; outputString "IN UNifyKindFun"
      ; return (a1,b1) }
unifyKindFun term x = failM 1
         [Ds "\nWhile infering the kind of the type\n   ",Dd term
         ,Ds "\nWe expected a kind arrow (_ ~> _),\n but inferred: "
         ,Dd x,Ds " instead"]

-- zap :: (Show c,Subsumption m b b) => c -> b -> Expected b -> m c
zap term rho (Check r) = do { morepoly (show term) rho r; return term }
zap term rho (Infer r) = do { a <- zonk rho; writeRef r a; return term }

zapPoly :: TyCh m => Tau -> PolyKind -> Expected Tau -> m Tau
zapPoly (term@(TyCon sx level_ s k)) (K sig) expect =
    do { (preds,rho) <- instanTy sig -- ## WHAT DO WE DO WITH THE PREDS?
       ; sig2 <- zonk sig
       ; (preds2,rho2) <- instanTy sig2  -- ## WHAT DO WE DO WITH THE PREDS?
       ; case rho of
            Rtau w -> mustBe ("Constructor","type") term w expect
            rho -> failM 0 [Ds "An unexpected Rho appeared while kind checking "
                           ,Dd term,Ds " :: ",Dd rho]
       }


zonkT :: TyCh m => Tau -> m Tau
zonkT = zonk

-- mustBe is a specialized version of zap, with better error reporting
mustBe :: TyCh m => (String,String) -> Tau -> Tau -> Expected Tau -> m Tau
mustBe (term,qual) t comput expect = handleM 1 (zap t comput expect) (errZap expect)
  where errZap :: TyCh m => (Expected Tau) -> String -> m a
        errZap (Check r) message =
         do { tz <- zonk t
            ; rz <- zonk r
            ; computz <- zonk comput
            ; failM 1
               [Ds ("\nWe computed the "++term++" ")
               ,Dd tz,Ds (" to have "++qual++" ")
               ,Dd computz,Ds "\nWe expected it to be "
               ,Dd rz,Ds ("\n"++message),
               if qual=="kind"
                  then Ds warning0 else Ds ""]
            }

warning0 =
 "\nThis sometimes happens when a constructor has (implicit) existential "++
 "type variables, whose kind is assumed to be *0."

------------------------------------------------------------
-- Now extend the basic Tau :: Tau, to other richer forms of types.

instance TyCh m => Typable m Rho Tau where
  tc (Rtau tau) expect = do { t <- tc tau expect; return(Rtau t)}
  tc (Rarrow x y) expect =
     do { a <- tc x expect; b <- tc y expect; return(Rarrow a b)}
  tc (Rpair x y) expect =
     do { a <- tc x expect; b <- tc y expect; return(Rpair a b)}
  tc (Rsum x y) expect =
     do { a <- tc x expect; b <- tc y expect; return(Rsum a b)}

instance TyCh m => Typable m Sigma Tau where
  tc (sigma@(Forall xs)) expect = do { ys <- tc xs expect; return(Forall ys)}

instance TyCh m => Typable m (L([Pred],Rho)) Tau where
  tc xs expect =
    do { (tvs,eqs,b) <- unBindWithL newflexi xs
       ; b2 <- tc b expect
       ; eqs2 <- mapM kindPred eqs
       ; (mapping,newbinders,body) <- subFreshNames tvs [] (eqs2,b2)
       ; return(windup newbinders body)
       }

instance TyCh m => Typable m (L([Pred],Tau)) Tau where
  tc xs expect =
    do { (tvs,eqs,b) <- unBindWithL newflexi xs
       ; b2 <- tc b expect
       ; eqs2 <- mapM kindPred eqs
       ; (mapping,newbinders,body) <- subFreshNames tvs [] (eqs2,b2)
       ; return(windup newbinders body)
       }

typkind (t@(Tv un f k)) = (t,k)

hasKind :: TyCh m => String -> Sigma -> Kind -> m ()
hasKind name sigma (MK kind) =
  do { let new nam quant k =
              do { v <- newFlexiTyVar k; return(TcTv v)}
     ; (env,eqs,rho) <- unBindWith new sigma
     ; let err message = failM 3
               [Ds ("\nWhile checking the kind of constructor\n   "++name++" :: ")
               ,Dl eqs ", ",Ds " =>\n      ",Dd rho, Dl (map typkind env) "\n", Ds message]
           err2 mess = err ("\nWe checked the well formedness of constraints, and found: "++mess)
           ok (Tv unq (Flexi ref) k) =
               do { maybet <- readRef ref
                  ; case maybet of
                      Nothing -> return True
                      Just t -> return False}
     ; good <- mapM ok env
     ; evars <- envTvs
     ; if (all id good)
          then if any (`elem` evars) env
                  then failM 2 [Ds "A universal variable escapes"]
                  else return ()
          else failM 2 [Ds "A universal variable got bound"]
     ; handleM 3 (check rho kind) err
     ; handleM 3 (mapM kindPred eqs) err2
     ; return ()
     }


--kindPred :: TyCh m => Pred -> m Pred
kindPred(Equality a b) =
  handleM 1 (do{(k1::Tau,t1) <- infer a; t2 <- check b k1; return(Equality t1 t2)})
    (\ s -> failM 0 [Ds "While checking equality constraint: "
                    ,Dd a,Ds " = ",Dd b,Ds ("\nkinds do not match"++s)])
kindPred (x@(Rel ts)) =
  do { ts2 <- check ts (Star LvZero)
     ; return(makeRel ts2)}

-----------------------------------------------------
-- A helper function for reporting errors when "morepoly" fails.

escapes2 [] = return ()
escapes2 bad = failM 0 [Dlf f bad "\n"]
  where f d (v@(Tv _ (Rigid All loc s) k),t) = displays d
           [Ds ("The explict typing: "++s)
           ,Ds ("\nAt "++show loc++" is too polymorphic.")
           ,Ds "\nThe variable ",Dd v
           ,Ds " must be instantiated to ",Dd t]
        f d (Tv _ (Rigid Ex loc s) k,t) = displays d
           [Ds ("An existential type var, arising from the pattern: "++ s)
           ,Ds (" at "++show loc++ " cannot be equal to "),Dd t]


captured sig1 sig2 rho mess =
  failM 0
    [Dd sig1,Ds " is not more polymorphic than\n"
    ,Dd sig2,Ds ("\n"++"Because the skolemized version of the second type: ")
    ,Dd rho,Ds ("\nhas the following problem: "++mess)]


----------------------------------------------------------------
-- Subsumption instances

instance TyCh m => Subsumption m Tau Tau where
   morepoly s x y = unify x y

instance (TypeLike m b,Subsumption m b b) => Subsumption m b (Expected b) where
   morepoly s t1 (Check t2) = morepoly s t1 t2
   morepoly s t1 (Infer r)  = do { a <- zonk t1; writeRef r a }

instance TyCh m => Subsumption m PolyKind PolyKind where
  morepoly s (K x) (K y) = morepoly s x y

instance TyCh m => Subsumption m Sigma Sigma where
  morepoly s sigma1 sigma2 =
     do { (skol_tvs,assump,rho) <- skolTy sigma2
        ; (preds,unifier) <- solveSomeEqs ("morepoly Sigma Sigma",starR) assump
        ; (_,residual::[Pred]) <-
             extractAccum (handleM 1 (assume preds unifier (morepoly s sigma1 rho))
                                     (captured sigma1 sigma2 rho))
        ; (tv1, level_) <- get_tvs sigma1   -- TODO LEVEL
        ; (tv2, level_) <- get_tvs sigma2   -- TODO LEVEL
        ; (tv3, level_) <- get_tvs residual -- TODO LEVEL
        ; let esc_tvs = tv1++tv2++tv3
              bad_tvs = filter (`elem` esc_tvs) skol_tvs
        ; case bad_tvs of
            [] -> injectA " morepoly Sigma Sigma " residual
            zs -> failM 0 [Ds "Not more poly",Dl zs ", "]
        }

instance TyCh m => Subsumption m Sigma (Expected Rho) where
   morepoly s s1 (Check e2) = morepoly s s1 e2
   morepoly s s1 (Infer ref) =
      do { (preds,rho1) <- instanTy s1;
         ; injectA " morepoly Sigma (Expected Rho) " preds -- ## DO THIS WITH THE PREDS?
         ; writeRef ref rho1
         }

instance (TyCh m) => Subsumption m Sigma Rho where
  morepoly = morepolySigmaRho

morepolySigmaRho s (Forall(Nil([],rho1))) rho2 = morepoly s rho1 rho2
morepolySigmaRho s (sigma1@(Forall sig)) rho2 =
     do { ts <- getTruths
        ; whenM False [Ds "Entering moreploy\n Sigma = "
               ,Dd sigma1,Ds "\n Rho = ",Dd rho2
               ,Ds "\n truths = ",Dl ts ", "]
        ; (vs,preds,rho1) <- instanL sig
        ; injectA " morepoly Sigma Rho 1 " preds -- ## DO THIS WITH THE PREDS?
        ; ((),oblig2) <- extract(morepoly s rho1 rho2)
        ; (local,general) <- localPreds vs oblig2
        -- ; warn [Ds "\nlocal = ",Dd local,Ds ", general = ", Dd general]
        ; (preds2,unifier) <- handleM 1 (solveSomeEqs ("morepoly Sigma Rho",rho2) local)
                                        (no_solution sigma1 rho2 rho1)
        ; gen2 <- sub ([],unifier,[],[]) general
        ; injectA " morepoly Sigma Rho 2 " (gen2++preds2)
        }

localPreds vs [] = return ([],[])
localPreds vs (p:ps) =
  do { (loc,gen) <- localPreds vs ps
     ; (free,_) <- get_tvs p
     ; if any (\ x -> elem x vs) free
          then return(p:loc,gen)
          else return(loc,p:gen) }

{-
norm :: TyCh a => Pred -> a [Pred]
norm (Equality x y) =
  do { -- outputString ("Normalizing "++show x++" and "++show y++"\n");
       a <- nfTau x
     ; b <- nfTau y
     ; ((),oblig2) <- extract(unify a b)
     ; return oblig2}
norm (Rel ts) =
  do { ts2 <- nfTau ts; return[makeRel ts2] }
-}


no_solution sigma rho skoRho s = failM 1
     [Ds "while checking that\n   ", Dd sigma
     ,Ds "\nwas more polymorphic than\n   ",Dd rho
     ,Ds "\nwe skolemized the second to get\n   ", Dd skoRho
     ,Ds ("\nbut, "++s)]



----------------------------------------------------------------

instance TyCh m => Subsumption m Rho Rho where
 morepoly s x y = f x y where
  f (Rarrow a b) x = do{(m,n) <- unifyFun x; morepoly s b n; morepoly s m a }
  f x (Rarrow m n) = do{(a,b) <- unifyFun x; morepoly s b n; morepoly s m a }
  f (Rpair m n) (Rpair a b) = do{ morepoly s m a; morepoly s n b }
  f (Rpair m n) x = do{(a,b) <- checkPair x; morepoly s m a; morepoly s n b}
  f x (Rpair a b) = do{(m,n) <- checkPair x; morepoly s m a; morepoly s n b}
  f (Rsum m n) (Rsum a b) = do{ morepoly s m a; morepoly s n b }
  f (Rsum m n) x = do{(a,b) <- checkSum x; morepoly s m a; morepoly s n b}
  f x (Rsum a b) = do{(m,n) <- checkSum x; morepoly s m a; morepoly s n b}
  f (Rtau x) (Rtau y) = (unify x y)

---------------------------------------------------

checkPair :: TyCh m => Rho -> m (Sigma,Sigma)
checkPair (Rtau x) =
   do { a <- newTau star
      ; b <- newTau star
      ; unify x (tpair a b)
      ; return (simpleSigma a,simpleSigma b) }
checkPair x = failM 0 [Ds "Expecting a pair type: ",Dd x]

checkSum :: TyCh m => Rho -> m (Sigma,Sigma)
checkSum (Rtau x) =
   do { a <- newTau star
      ; b <- newTau star
      ; unify x (tsum a b)
      ; return (simpleSigma a,simpleSigma b) }
checkSum x = failM 0 [Ds "Expecting a sum type: ",Dd x]


showPred xs = plistf g "{" xs ", " "}"
  where g (Equality x y) = "Equal "++ show x ++ " " ++ show y
        g (Rel ts) = show ts


showPairs xs = plistf g "{" xs ", " "}"
  where g (x,y) = show x ++ " = " ++ show y

extract :: TyCh m => m a -> m (a,[Pred])
extract comp = do { (a,eqs) <- extractAccum comp
                   ; eqs2 <- zonk eqs; return(a,eqs2) }

--------------------------------------------------------------------------
--------------------------------------------------------------------------
-- Parsing types. Note that we parse type PT, and then translate

data PPred = Equality' PT PT |  Rel' String PT

data PT
  = TyVar' String
  | Rarrow' PT PT
  | Karrow' PT PT
  | TyApp' PT PT
  | TyFun' [PT]
  | TyCon' String
  | Star' Int
  | Forallx Quant [(String,PT,Quant)] [PPred] PT
  | Tlamx String PT
  | AnyTyp -- Gen up a new var with universe polymorphic kind
  | Ext (Extension PT)

-------------------------------------------
univLevelFromPTkind (Star' n) = n
univLevelFromPTkind (Karrow' dom rng) = univLevelFromPTkind rng
univLevelFromPTkind (Forallx q vs preds t) = univLevelFromPTkind t
univLevelFromPTkind x = 0

---------------------------------------------

instance Eq PPred where
  (Equality' pt1 pt2)==(Equality' pt3 pt4) = pt1==pt3 && pt2==pt4
  (Rel' s1 pt1) == (Rel' s2 pt2) = s1==s2 && pt1==pt2
  _ == _  = False

instance Eq PT where
  (TyVar' s1)==(TyVar' s2) = s1==s2
  (Rarrow' pt1 pt2)==(Rarrow' pt3 pt4) = pt1==pt3 && pt2==pt4
  (Karrow' pt1 pt2)==(Karrow' pt3 pt4) = pt1==pt3 && pt2==pt4
  (TyApp' pt1 pt2)==(TyApp' pt3 pt4) = pt1==pt3 && pt2==pt4
  (TyFun' pts1)==(TyFun' pts2) = pts1==pts2
  (TyCon' s1)==(TyCon' s2) = s1==s2
  (Star' i1)==(Star' i2) = i1==i2
  (Ext x) == (Ext y) = x==y
  (Forallx q1 xs1 pps1 pt1) == (Forallx q2 xs2 pps2 pt2) =
    q1==q2 && (and $ zipWith f xs1 xs2) && pps1==pps2 && pt1==pt2
    where
    f (s1,pt1,q1) (s2,pt2,q2) =
          s1==s2 && pt1==pt2 && q1==q2
  (Tlamx s1 pt1)==(Tlamx s2 pt2) = s1==s2 && pt1==pt2
  AnyTyp == AnyTyp = True
  _ == _ = False

---------------------------------------------
getFreeL bnd t free = union (getFree bnd t) free

getFree :: [String] -> PT -> [String]
getFree bnd (TyVar' s) = if elem s bnd then [] else [s]
getFree bnd (Rarrow' x y) = union (getFree bnd x) (getFree bnd y)
getFree bnd (Karrow' x y) = union (getFree bnd x) (getFree bnd y)
getFree bnd (TyFun' (x:xs)) = foldr (getFreeL bnd) [] xs
    -- Note that the object in function position (x) is like a TyCon
getFree bnd (TyApp' x y) = (getFree bnd x) `union` (getFree bnd y)
getFree bnd (TyCon' s) = []
getFree bnd (Star' n) = []
getFree bnd (Tlamx n t) = getFree (n:bnd) t
getFree bnd (AnyTyp) = []
getFree bnd (Ext x) = foldr (getFreeL bnd) [] (extList x)
getFree bnd (Forallx q xs eqs t) = f bnd xs t `union` g bnd xs eqs
  where f bnd [] t = getFree bnd t
        f bnd ((s,a,q):xs) t = (getFree bnd a) `union` (f (s:bnd) xs t)

        g bnd ((s,a,q):xs) ys = g (s:bnd) xs ys
        g bnd [] ((Equality' a b):xs) = (getFree bnd a) `union` (getFree bnd b) `union` g bnd [] xs
        g bnd [] ((Rel' nm ts):xs) = (getFree bnd ts)  `union` (g bnd [] xs)
        g bnd _ [] = []

        h bnd t free = union (getFree bnd t) free

getFreePred bnd (Equality' x y) = getFree bnd x `union` getFree bnd y
getFreePred bnd (Rel' nm ts) =  getFree bnd ts

getFreePredL bnd xs = foldr g [] xs
    where g t free = union (getFreePred bnd t) free


-- Get all the variables appearing in the type, both free and bound

getFL union t free = union (getF union t) free

getF :: ([String]->[String]->[String]) -> PT -> [String]
getF union (TyVar' s) = [s]
getF union (Rarrow' x y) = union (getF union x) (getF union y)
getF union (Karrow' x y) = union (getF union x) (getF union y)
getF union (TyFun' (x:xs)) = foldr (getFL union) [] (xs)
getF union (TyApp' x y) = (getF union x) `union` (getF union y)
getF union (TyCon' s) = []
getF union (Star' n) = []
getF union (Tlamx n t) = getF union t
getF union (AnyTyp) = []
getF union (Ext x) = foldr (getFL union) [] (extList x)
getF union (Forallx q xs eqs t) = f xs t `union` g eqs
  where f [] t = getF union t
        f ((s,a,q):xs) t = (getF union a) `union` (f xs t)
        g [] = []
        g ((Equality' a b):xs) = (getF union a) `union` (getF union b) `union` g xs
        g ((Rel' nm ts):xs) =(getF union ts) `union` (g xs)


getAll = getF union
getMult = getF (++)


subPT :: Monad m => [(String,String)] -> (String -> m String) -> PT -> m PT
subPT sigma fresh x =
 let rcall x = subPT sigma fresh x
 in case x of
  (TyVar' s) -> case lookup s sigma of
                 Just t -> return(TyVar' t)
                 Nothing -> return(TyVar' s)
  (Rarrow' x y) -> do { a <- rcall x; b <- rcall y; return(Rarrow' a b)}
  (Karrow' x y) -> do { a <- rcall x; b <- rcall y; return(Karrow' a b)}
  (TyFun' xs)   -> do { ys <- mapM rcall xs; return(TyFun' ys)}
  (TyApp' x y)  -> do { a <- rcall x; b <- rcall y; return(TyApp' a b)}
  (Ext x) -> do { a <- extM rcall x; return(Ext a)}
  (TyCon' s) -> return(TyCon' s)
  (Star' n) -> return(Star' n)
  (AnyTyp) -> return(AnyTyp)
  (Tlamx n t) ->
    do { m <- fresh n
       ; s <- subPT ((n,m):sigma) fresh t
       ; return(Tlamx m s)}
  (Forallx quant xs eqs t) ->
    do { let fresh1 (x,y,z) = do { x1 <- fresh x; return(x,x1)}
             g (x,y,z) (_,x1) = (x1,y,z)
       ; xs1 <- mapM fresh1 xs
       ; let sigma1 = xs1 ++ sigma
             rcall1 x = subPT sigma1 fresh x
             f (Equality' x y) = do { a <- rcall1 x; b <- rcall1 y; return(Equality' a b)}
             f (Rel' nm ts) = do { ys <- rcall1 ts; return(Rel' nm ys)}
       ; eqs1 <- mapM f eqs
       ; t1 <- rcall1 t
       ; return(Forallx quant (zipWith g xs xs1) eqs1 t1)}

-- Apply a substitution, but don't rename any of the binding
-- occurences. The user must be sure that this doesn't matter.
ptsub :: [(String,PT)] -> PT -> PT
ptsub sigma x =
 let rcall x = ptsub sigma x
 in case x of
  (TyVar' s) -> case lookup s sigma of {Just t -> t; Nothing -> TyVar' s}
  (Rarrow' x y) -> Rarrow' (rcall x) (rcall y)
  (Karrow' x y) -> Karrow' (rcall x) (rcall y)
  (TyFun' xs)   -> TyFun'(map rcall xs)
  (TyApp' x y)  -> TyApp' (rcall x) (rcall y)
  (Ext x) -> Ext(fmap rcall x)
  (TyCon' s) -> (TyCon' s)
  (Star' n) -> (Star' n)
  (AnyTyp) -> (AnyTyp)
  (Tlamx n t) -> Tlamx n (ptsub ((n,TyVar' n):sigma) t)
  (Forallx quant xs eqs t) ->
   let sub1 (nm,kind,quant) = (nm,ptsub sigma kind,quant)
       sub2 (Equality' t1 t2) = Equality' (rcall t1) (rcall t2)
       sub2 (Rel' nm ts) = Rel' nm (rcall ts)
    in Forallx quant (map sub1 xs) (map sub2 eqs) (rcall t)

ppredsub sub (Equality' x y) = Equality' (ptsub sub x) (ptsub sub y)
ppredsub sub (Rel' x y) = Rel' x (ptsub sub y)

--------------------------------------------------------------------
-- Translating. The translation respects (and enforces) the 3 level
-- distinctions between Sigma, Rho and Tau.

type ToEnv = [(String,Tau,PolyKind)]
type TransEnv = (ToEnv,Loc,[SynExt String])

toSigma :: TyCh m => TransEnv -> PT -> m(Sigma,[(String,Name)])
toSigma env (Forallx All xs eqs body) =
   do { (ns,fargs,env2) <- argsToEnv xs env
      ; eqs2 <- toEqs env2 eqs
      ; r <- toRho env2 body
      ; return(Forall (windup fargs (eqs2,r)),ns) }
toSigma env x = do { r <- toRho env x; return(Forall (Nil ([],r)),[])}

toEqs :: TyCh m => TransEnv -> [PPred] -> m [Pred]
toEqs env [] = return []
toEqs env ((Equality' a b):xs) =
  do { -- warn [Ds "Env = \n   ",Dl (take 7 env) "\n  ",Dd a, Dd b]
       m <- toTau env a
     ; n <- toTau env b
     ; ys <- toEqs env xs
     ; return((Equality m n):ys) }
toEqs env ((Rel' nm ts):xs) =
  do { zs <- toTau env ts
     ; ys <- toEqs env xs
     ; return((makeRel zs):ys) }


toRho env (Rarrow' x y) =
  do { (s,_) <- toSigma env x; r <- toRho env y; return(arrow s r)}
toRho env (TyApp' (TyApp' (TyCon' "(,)") x) y) =
  do { (a,_) <- toSigma env x; (b,_) <- toSigma env y; return(pair a b)}
toRho env (TyApp' (TyApp' (TyCon' "(+)") x) y) =
  do { (a,_) <- toSigma env x; (b,_) <- toSigma env y; return(rsum a b)}
toRho env t = do { w <- toTau env t; return(Rtau w) }

nonCon x | x==infixEqName = True
nonCon (x:xs) = isLower x
nonCon x = False

-- whenever we translate to a Tau we need a count of how many TyApp nodes
-- we are under, because if we find a TySyn its arity must match the number
-- of nodes we are under. The parameter "n" counts this number. Note how
-- in most recursive calls it is 0.

toTau env x = readTau 0 env x

readTau :: TyCh m => Int -> TransEnv -> PT -> m Tau
readTau n env (TyVar' s) = readName "\nWhile parsing a type var," env s
readTau n env (Rarrow' x y) =
  do { s <- readTau 0 env x; r <- readTau 0 env y; return(tarr s r)}
readTau n env (Karrow' x y) =
  do { s <- readTau 0 env x; r <- readTau 0 env y; return(Karr s r)}
readTau n env (TyCon' (tag@('`':cs))) = return (ttag tag)
readTau n env (TyCon' s) =
  do { x <- readName "\nWhile parsing a type constructor," env s
     ; case x of
        (TySyn nm m fs as x) | m>n -> failM 0 [Ds ("Type synonym: "++nm++" applied to few args")]
        (TySyn nm m fs as x) | m<n -> failM 0 [Ds ("Type synonym: "++nm++" applied to many args")]
        x -> return x }
readTau n env (Star' m) = return(Star (lv m))
readTau n env (TyApp' x y) =
  let (funtyp,argtyps) = root x [y]
  in do { f <- readTau (length argtyps) env funtyp
        ; xs <- mapM (readTau 0 env) argtyps
        ; case f of
           (TySyn nm m fs as b) ->
               do { let subst = zipWith (\ (nm,k) t -> (nm,t)) fs xs
                  ; body <- sub (subst,[],[],[]) b
                  ; return(TySyn nm n fs xs body)}
           _ -> return(applyT (f:xs)) }
readTau n env (ty@(TyFun' (x:xs))) =
  do { s <- readTau 0 env x
     -- ; d1 <- warnM [Ds "\n Entering ",Dd ty,Ds "\n",Dl env ","]
     ; ys <- mapM (readTau 0 env) xs
     ; case s of
        TyCon sx level_ nm k | nonCon nm -> return(TyFun nm k ys)
        TyCon sx level_ nm k -> failM 0 [Ds ("The name of a type function must begin with a lower case letter: "++nm)]
        _ -> failM 0 [Ds "\n",Dd ty
                     ,Ds " doesn't have a type function name in the function position of type function application: "
                     ,Dd s,Ds ("   "++sht s)]}
readTau n env (AnyTyp) = newUniv
readTau n env (t@(Forallx Ex xs eqs body)) =
   do { (_,fargs,env2) <- argsToEnv xs env
      ; r <- readTau 0 env2 body
      ; eqs2 <- toEqs env2 eqs
      ; return(TyEx(windup fargs (eqs2,r))) }
readTau n env (Forallx All [] [] body) = readTau n env body
readTau n env (t@(Forallx q xs eqs body)) =
  failM 1 [Ds "\n\nSigma type in Tau context: ", Dd t]
readTau n env (t@(Tlamx s x)) = failM 1 [Ds "No lambda types in rankN: ",Dd t]
readTau n env (Ext x) =
  do { exts <- syntaxInfo
     ; loc <- currentLoc
     ; let lift0 t = TyCon' t
           lift1 t x = TyApp' (TyCon' t) x
           lift2 t x y = TyApp' (TyApp' (TyCon' t) x) y
           inject s = failM 2 [Ds ("\nChrSeq literals are not types: #\""++s++"\".")]
     ; new <- buildExt (show loc) (lift0,lift1,lift2,inject) x exts
     ; readTau n env new
     }


root (TyApp' f y) ys = root f (y:ys)
root f ys = (f,ys)

argsToEnv :: TyCh m => [(String,PT,Quant)] -> TransEnv -> m ([(String,Name)],ForAllArgs,TransEnv)
argsToEnv [] env = return([],[],env)
argsToEnv ((s,k,quant):xs) (env@(toenv,loc,exts)) =
 do { w <- toTau env k
    ; let k2 = MK w
    ; nm <- fresh
    ; (ns,zs,env2) <- argsToEnv xs ((s,TyVar nm k2,poly k2):toenv,loc,exts)
    ; return ((s,nm):ns,(nm,k2,quant):zs,env2)
    }

------------------------------------------------------
tunit' = TyCon' "()"

prodT' = TyCon' "(,)"
prod' x y = TyApp' (TyApp' prodT' x) y
tprods' [t] = t
tprods' (x:xs) = prod' x (tprods' xs)

sumT' = TyCon' "(+)"
sum' x y = TyApp' (TyApp' sumT' x) y
tsums' [t] = t
tsums' (x:xs) = sum' x (tsums' xs)

listT' = TyCon' "[]"
list' x = TyApp' listT' x

arr' x y = Rarrow' x y

applyT' [t] = t
applyT' [TyCon' "(->)",x,y] = Rarrow' x y
applyT' [x,y] = TyApp' x y
applyT' (x : y : z) = applyT' ((TyApp' x y):z)

------------------------------------------------------------------
-- parsing simple types, ones that never need parenthesizing

parse_tag inject =
     try (do { whiteSpace
             ; (char '`')
             ; v <- ident
             ; notFollowedBy (char '`')
             ; whiteSpace
             ; return(inject v)})
  where ident = do{ c <- identStart tokenDef
                  ; cs <- many (identLetter tokenDef)
                  ; return (c:cs)
                  } <?> "identifier"

simpletyp ::Parser PT
simpletyp =
       (fmap TyCon' constructorName)                   -- T
   <|> (parse_tag (\ s -> TyCon' ("`"++s)))            -- `abc
   <|> (fmap TyVar' identifier)                        -- x
   <|> parseStar                                       -- * *1 *2
   <|> (do { x <- extP typN; return(Ext x)})           -- #"abc"   #[x,y : zs]i   #4i   #(2+x)i    #(a,b,c)i
   <|> try (fmap TyCon'(symbol "()" <|> symbol "[]"))  -- () and []
   <|> try (do { x <- parens(symbol "->" <|>           -- (->) (+) (,) and (==)
                             symbol "+"  <|>
                             symbol ","  <|>
                             symbol "==")
               ; return(TyCon' ("("++x++")"))})
   <|> try(do {ts <- parens(sepBy1 typN (symbol ","))  -- (t,t,t)
              ; return (tprods' ts)})
   <|> try(do {ts <- parens(sepBy1 typN (symbol "+"))  -- (t+t+t)
              ; return (tsums' ts)})
   <|> do {t <- squares typN; return (list' t)}        -- [t]
   <|> (do { xs <- braces (many1 simpletyp); return(TyFun' xs)}) -- {f x y}
   <|> (do { n <- natural
           ; fail (show n++" is not a type. Use #"++show n++" for Nat constants")})


parseStar :: Parser PT
parseStar = lexeme(do{char '*'; ds <- many digit; return(Star' (val ds))})
  where val :: String -> Int
        val [] = 0
        val xs = read xs

data ArrowSort
  = Single   -- ->
  | Wavy     -- ~>
  | Fat      -- =>
  | InfixEq  -- ==

arrTyp :: Parser PT
arrTyp =
   do { ts <- many1 (simpletyp)-- "f x y -> z"  parses as "(f x y) -> z"
      ; let d = (applyT' ts)     -- since (f x y) binds tighter than (->)
      ; range <- possible
           ((do {symbol "->"; ans <- typN; return(Single,ans)})  <|>
            (do {symbol "~>"; ans <- typN; return(Wavy,ans)})    <|>
            (do {symbol "=="; ans <- typN; return(InfixEq,ans)})
           )
      ; case range of
           Nothing -> return d
           Just(Single,r) -> return(Rarrow' d r)
           Just(Wavy,r) -> return(Karrow' d r)
           Just(InfixEq,r) -> return(TyFun' [TyCon' infixEqName,d,r])
      }

allPrefix:: Parser (Quant,[(String,PT,Quant)])
allPrefix =
    do { q2 <- ((reserved "forall") >> (return All)) <|>
               ((reserved "exists") >> (return Ex))
       ; ns <- many1 (argument All)
       ; symbol "."
       ; return(q2,ns)
       }

allTyp :: Parser PT
allTyp =
  do { (q2,ns) <- allPrefix
     ; eqs <- props
     ; t <- typN
     ; return (Forallx q2 ns eqs t)
     }

argument:: Quant -> Parser(String,PT,Quant)
argument q =
  (do { x <- identifier; return(x,AnyTyp,q)})  <|>
  (parens (do { x <- identifier
              ; (reservedOp "::")
              ; k <- typN
              ; return(x,k,q)}))


typN :: Parser PT
typN = allTyp <|> arrTyp <|> parens (typN)

------------------------------------------------

qual = (reservedOp "="  >> return "=" )

-- A proposition looks like:  t1 = t2,  t1 != t2, or   T t1 t2 t3

proposition =
 do { t1 <- typN
    ; rest <- (possible (do { t <- qual; x <- arrTyp; return(t,x)}))
    ; case rest of
        Just("=",t2)  -> return(Equality' t1 t2)
        Nothing -> case isTyConAp t1 of
                     Just nm -> return(Rel' nm t1)
                     Nothing -> fail "not prop"
    }

isTyConAp (TyApp' (TyApp' (TyCon' "(,)") x) y) = Nothing
isTyConAp (TyApp' (TyCon' t) x) = Just t
isTyConAp (TyApp' (TyVar' t) x) = Just t
isTyConAp (TyApp' f x) = isTyConAp f
isTyConAp x = Nothing

props :: Parser [PPred]
props = (try (do { x <- proposition; symbol "=>"; return[x]})) <|>
          (try (do { xs <- parens(sepBy (proposition) comma)
                   ; symbol "=>"; return xs}))                     <|>
          (return [])


typToRel t (TyApp' (TyCon' nm) x) = return(Rel' nm t)
typToRel t (TyApp' f x) = typToRel t f
typToRel t (TyCon' nm) = return(Rel' nm t)
typToRel t _ = fail ("Expecting a relational predicate, found:\n  "++ show t)


-- A typing has many forms, some are listed below
-- f :: a -> b                              simple
-- f :: P a => a -> b                       qualified
-- f :: a=b => a -> b                       equality qualified
-- f :: a!=b => a -> b                      disequality
-- f :: (a=b,P a) => a -> b                 multiply qualified
-- f :: forall a b . (a=b,P a) => a -> b    explicit forall

typingHelp =
  do { reservedOp "::"
     ; prefix <- possible (allPrefix)
     ; preds <- props
     ; body <- typN
     ; return(prefix,preds,body)
     }

typing =
  do { (prefix,preds,body) <- typingHelp
     ; case prefix of
        Nothing -> let predfree = getFreePredL [] preds
                       bodyfree = getFree [] body
                       free = nub(predfree++bodyfree)
                       f x = (x,AnyTyp,All)
                   in return(Forallx All (map f free) preds body)
        Just(q2,ns) -> return (Forallx q2 ns preds body)
     }

--------------------------------------------------------

pt s = case parse2 (typN) s of { Right(x,more) -> x; Left s -> error (show s) }
parsePT = pt

intThenTyp n = do { m <- token(possible natural); t <- typN; return (pick m,t)}
  where pick Nothing = (n::Int)
        pick (Just i) = fromInteger i

parseType s =
  case parse2 typN s of
    Right(x,more) -> return x
    Left s -> failM 1 [Ds "Ill-formed type in input.\n",Ds s]

parseIntThenType n s =
  case parse2 (intThenTyp n) s of
      Right(x,more) -> return x
      Left s -> failM 1 [Ds "Ill-formed type in input.\n",Ds s]

peqt s = case parse2 (arrTyp) s of { Right(x,more) -> x; Left s -> error s }

k = "forall a b . a -> b -> b"
f1 = "(Int -> Int -> Int) -> Int"
f2 = "(forall x . x -> x -> x) -> Int"
g = "((forall x . [x] -> [x]) -> Int) -> Int"
k1 = "(forall a . a -> a) -> Int"
k2 = "([Int] -> [Int]) -> Int"


-- Pairs for running subsumption tests
subpairs =
  [("Int","Int")
  ,("Int -> Bool","Int -> Bool")
  ,("forall a . a -> a","Int -> Int")
  ,("forall a . a -> a","forall b . [b] -> [b]")
  ,("forall a . a -> a","forall b c . (b,c) -> (b,c)")
  ,("forall a b . (a,b) -> (b,a)","forall c . (c,c) -> (c,c)")
  --,("Bool -> (forall a . a -> a)","Bool -> Int -> Int") --Not legal type
  ,("(Int -> Int) -> Bool","(forall a . a -> a) -> Bool")
  ,("(forall b . [b]->[b]) -> Bool","(forall a . a -> a) -> Bool")
  ,("(Int -> Int -> Int) -> Int","(forall x . x -> x -> x) -> Int")
  ,("(forall a . [a],forall a . a -> a)","([Int],Int -> Int)")
  --,("([Int],Int -> Int)","(forall a . [a],forall a . a -> a)") -- Not subsumed
  ]

-----------------------------------------------------------------------


instance NameStore d => Exhibit d PPred where
  exhibit d (Equality' x y) = (d,"Equal "++show x++" "++show y)
  exhibit d (Rel' nm ts) = (d,show ts)

instance NameStore d => Exhibit d PT where
  exhibit d x = (d,show x)


instance Show PT where
  show (TyVar' s) = s
  show (Rarrow' x y) = showp x ++ " -> "++show y
  show (Karrow' x y) = showp x ++ " ~> "++show y
  show (TyApp' (TyCon' "[]") x) = "[" ++ show x ++ "]"
  show (TyApp'(TyApp'(TyCon' "(,)") x) y)= "("++show x++","++show y++")"
  show (TyApp'(TyApp'(TyCon' "(+)") x) y)= "("++show x++"+"++show y++")"
  show (TyApp'(TyApp'(TyCon' "(!=)") x) y)= show x++" != "++show y
  show (TyApp' x (y@(TyApp' _ _))) = show x ++ " " ++ showp y
  show (TyApp' x y) = show x ++ " " ++ showp y
  show (TyCon' s) = s
  show (TyFun' xs) = plistf f "{" xs " " "}"
    where f (x@(TyApp' _ _)) = "("++show x++")"
          f (x@(Rarrow' _ _)) = "("++show x++")"
          f (x@(Karrow' _ _)) = "("++show x++")"
          f x = show x
  show (Star' n) = "*"++show n
  show (Tlamx n t) = "("++n++" . "++show t++")"
  show (AnyTyp) = "?"
  show (Forallx q2 xs eqs t) = showquant q2 ++ f xs++ g eqs ++ show t ++ ")"
    where f [(s,AnyTyp,q)] =  shq q ++ s ++ " . "
          f ((s,AnyTyp,q):xs) = shq q++ s ++ " "++f xs
          f [(s,k,q)] = "("++  shq q++ s ++"::" ++ show k ++") . "
          f ((s,k,q):xs) = "("++  shq q ++ s++"::" ++ show k ++") "++f xs
          f [] = ""
          g [] = ""
          g xs = plistf show "(" xs "," ") => "
          shq All = ""
          shq Ex  = "_"

instance Sht PT where
  shtt (TyVar' s) = "(TyVar' "++s++ ")"
  shtt (Rarrow' x y) = shtt x ++ " -> "++shtt y
  shtt (Karrow' x y) = shtt x ++ " ~> "++shtt y
  shtt (TyApp' x y) = "(TyApp' "++shtt x ++ " " ++ shtt y++")"
  shtt (TyCon' s) =  "(TyCon' "++s++ ")"
  shtt (TyFun' xs) = plistf f "{" xs " " "}"
    where f (x@(TyApp' _ _)) = "("++shtt x++")"
          f (x@(Rarrow' _ _)) = "("++shtt x++")"
          f (x@(Karrow' _ _)) = "("++shtt x++")"
          f x = shtt x
  shtt (Star' n) = "*"++show n
  shtt (Tlamx n t) = "("++n++" . "++shtt t++")"
  shtt (AnyTyp) = "AnyTyp"
  shtt (Forallx q2 xs eqs t) =  "(Forallx ... )"

showquant All = "(forall "
showquant Ex = "(exists "

showp x@(Rarrow' _ _) = "("++show x ++ ")"
showp x@(Karrow' _ _) = "("++show x ++ ")"
showp (t@(TyApp' (TyCon' "[]") x)) = show t
showp (t@(TyApp'(TyApp'(TyCon' "(,)") x) y)) = show t
showp (t@(TyApp'(TyApp'(TyCon' "(+)") x) y)) = show t
showp x@(TyApp' _ _) = "("++show x ++ ")"
showp x@(Forallx q _ _ _) = "("++show x ++ ")"
showp x = show x




--------------------------------------------------------------
-- show instances

isRow :: Tau -> Bool
isRow (TyApp (TyApp (TyCon sx _ "RCons" _) x) y) = True
isRow (TyCon sx _ "RNil" _) = True
isRow _ = False

rowElem :: Tau -> [Tau] -> Either [Tau] ([Tau],Tau)
rowElem (TyCon sx _ "RNil" _) es = Left (reverse es)
rowElem (TyApp (TyApp (TyCon sx _ "RCons" _) e) y) es = rowElem y (e:es)
rowElem x es = Right(reverse es,x)

unsafeUnwind :: Swap a => L a -> ([(Name,Kind,Quant)],a)
unsafeUnwind (Nil t) = ([],t)
unsafeUnwind (Cons (k,q) b) = ((x,k,q):xs,t)
   where (x,rest) = unsafeUnBind b
         (xs,t) = unsafeUnwind rest

-------------------------------------------------------------------------
-- is one Tau a subterm of another Tau?

instance Eq Tau where
  (TyVar n _) == (TyVar m _) = n==m
  (TyApp a b) == (TyApp m n) = a==m && b==n
  (TyCon sx l n _) == (TyCon tx k m _) = l==k && n==m
  (Star n) == (Star m) = n==m
  (Karr a b) == (Karr m n) = a==m && b==n
  (TyFun f _ as) == (TyFun g _ bs) = f==g && as==bs
  (TcTv x) == (TcTv y) = x==y
  (TySyn nm n fs as x) == y = x==y
  y == (TySyn nm n fs as x) = x==y
  _ == _ = False

instance Ord Tau where
  compare (TySyn nm n fs as x) y = compare x y
  compare y (TySyn nm n fs as x) = compare y x

  compare (TyVar n _) (TyVar m _) = compare n m
  compare (TyVar _ _) _ = LT
  compare _ (TyVar _ _) = GT

  compare (TcTv x) (TcTv y) = compare x y
  compare (TcTv x) _ = LT
  compare _ (TcTv y) = GT

  compare (TyCon sx l n _) (TyCon tx k m _) = case compare n m of EQ -> compare l k ; o -> o
  compare (TyCon sx _ n _) _ = LT
  compare _ (TyCon sx _ m _) = GT

  compare (Star n) (Star m) = compare n m
  compare (Star n) _ = LT
  compare _ (Star m) = GT

  compare (TyApp a b) (TyApp m n) = if a==m then compare b n else compare a m
  compare (TyApp a b) _ = LT
  compare _ (TyApp a b) = GT

  compare (Karr a b) (Karr m n) = if a==m then compare b n else compare a m
  compare (Karr a b) _ = LT
  compare _ (Karr a b) = GT

  compare (TyFun f _ as) (TyFun g _ bs) = compare as bs
  compare (TyFun f _ as) _ = LT
  compare _ (TyFun g _ bs) = GT

  compare x y = error ("Can't compare: "++show x++" and "++show y)

instance Eq Pred where
  (Rel x) == (Rel y) = x==y
  (Equality x y) == (Equality a b) = (x==a) && (y==b)
  x == y = False

---------------------------------------------------------------
-----------------------------------------------------------
-- Side-effect Free subsitution. Usually you must zonk
-- before calling this function.

subKind :: [(TcTv,Tau)] -> Kind -> Kind
subKind [] x = x
subKind env (MK x) = MK(subTau env x)

subPoly :: [(TcTv,Tau)] -> PolyKind -> PolyKind
subPoly [] x = x
subPoly env (K s) = K(subSigma env s)

subSigma :: [(TcTv,Tau)] -> Sigma -> Sigma
subSigma [] x = x
subSigma env (Forall xs) = Forall(subL env xs)

subL :: [(TcTv,Tau)] -> L ([Pred],Rho) -> L ([Pred],Rho)
subL [] xs = xs
subL env (Nil(eqn,rho)) = Nil(subPred env eqn,subRho env rho)
subL env (Cons (k,q) x) = Cons (subKind env k,q) (bind nm xs)
  where (nm,more) = unsafeUnBind x
        xs = subL env more

subLTau :: [(TcTv,Tau)] -> L ([Pred],Tau) -> L ([Pred],Tau)
subLTau [] xs = xs
subLTau env (Nil(eqn,rho)) = Nil(subPred env eqn,subTau env rho)
subLTau env (Cons (k,q) x) = Cons (subKind env k,q) (bind nm xs)
  where (nm,more) = unsafeUnBind x
        xs = subLTau env more

subPred :: [(TcTv,Tau)] -> [Pred] -> [Pred]
subPred [] xs = xs
subPred env xs = map f xs
   where f (Equality x y) = Equality (subTau env x) (subTau env y)
         f (Rel ts) = makeRel (subTau env ts)

subPairs :: [(TcTv,Tau)] -> [(Tau,Tau)] -> [(Tau,Tau)]
subPairs [] xs = xs
subPairs env xs = map f xs where f (x,y) = (subTau env x,subTau env y)


subRho :: [(TcTv,Tau)] -> Rho -> Rho
subRho [] x = x
subRho env (Rarrow s r) = Rarrow (subSigma env s) (subRho env r)
subRho env (Rpair s r) = Rpair (subSigma env s) (subSigma env r)
subRho env (Rsum s r) = Rsum(subSigma env s) (subSigma env r)
subRho env (Rtau t) = Rtau(subTau env t)

subTau :: [(TcTv,Tau)] -> Tau -> Tau
subTau [] x = x
subTau env (TcTv (x@(Tv unq flav k))) =
   case lookup x env of
      Nothing -> TcTv (Tv unq flav (subKind env k))
      Just z -> z
subTau env (TyApp x y) =  TyApp (subTau env x) (subTau env y)
subTau env (TyCon sx l s k) = TyCon sx l s k2
  where k2 = subPoly env k
subTau env (Star n) = Star n
subTau env (Karr x y) =  Karr (subTau env x) (subTau env y)
subTau env (TyFun f k x) = TyFun f (subPoly env k) (map (subTau env) x)
subTau env (TyVar s k) = TyVar s (subKind env k)
subTau env (TySyn nm n fs as x) = TySyn nm n (map f fs) (map (subTau env) as) (subTau env x)
  where f (nm,k) = (nm,subKind env k)
subTau env (TyEx e) = TyEx(subLTau env e)

---------------------------------------------------
-- Get type variables from a term, should be zonked first

union2 (x,y) (a,b) = (union x a,unionBy f y b)
  where f (n1,k1) (n2,k2) = n1==n2

union3 (x,y,z) (a,b,c) = (union x a,unionBy f y b,union z c)
  where f (n1,k1) (n2,k2) = n1==n2


varsOfTau :: Tau -> ([TcTv],[(Name,Kind)],[TcLv])
varsOfTau (TcTv x) = ([x],[],[])
varsOfTau (TyApp x y) = union3 (varsOfTau x) (varsOfTau y)
varsOfTau (TyCon sx l s k) = varsOfPoly k `union3` varsOfLevel l
varsOfTau (Star n) = ([],[],[])
varsOfTau (Karr x y) = union3 (varsOfTau x) (varsOfTau y)
varsOfTau (TyFun f k xs) = union3 (varsOfPoly k) (foldr g ([],[],[]) xs)  where g t vs = union3 (varsOfTau t) vs
varsOfTau (TyVar s k) = union3 ([],[(s,k)],[]) (varsOfKind k)
varsOfTau (TySyn nm n fs xs x) =
      union3 (varsOfTau x)
            (union3 (foldr h ([],[],[]) fs) (foldr g ([],[],[]) xs))
   where g t vs = union3 (varsOfTau t) vs
         h (nm,k) vs = union3 (varsOfKind k) vs
varsOfTau (TyEx x) = (varsOfLTau x)

varsOfPoly(K x) = varsOfSigma x

varsOfKind (MK x) = varsOfTau x

varsOfSigma (Forall z) = varsOfL z

varsOfL :: L ([Pred],Rho) -> ([TcTv],[(Name,Kind)],[TcLv])
varsOfL (Nil(eqns,rho)) = union3 (varsOfPred eqns) (varsOfRho rho)
varsOfL (Cons (k,q) x) = union3 (varsOfKind k) (rem (varsOfL  more))
  where (nm,more) = unsafeUnBind x
        rem (x,y,z) = (x,remove y,z)
        remove [] = []
        remove ((n,k):xs) | n==nm = remove xs
        remove (x:xs) = x:(remove xs)

varsOfLTau :: L ([Pred],Tau) -> ([TcTv],[(Name,Kind)],[TcLv])
varsOfLTau (Nil(eqns,rho)) = union3 (varsOfPred eqns) (varsOfTau rho)
varsOfLTau (Cons (k,q) x) = union3(varsOfKind k) (rem(varsOfLTau more))
  where (nm,more) = unsafeUnBind x
        rem (x,y,z) = (x,remove y,z)
        remove [] = []
        remove ((n,k):xs) | n==nm = remove xs
        remove (x:xs) = x:(remove xs)

varsOfPred [] = ([],[],[])
varsOfPred ((Equality x y):xs) = union3 (union3 (varsOfTau x) (varsOfTau y)) (varsOfPred xs)
varsOfPred ((Rel ts):xs) = union3 (varsOfTau ts) (varsOfPred xs)

varsOfRho (Rarrow x y) = union3 (varsOfSigma x) (varsOfRho y)
varsOfRho (Rpair x y) = union3 (varsOfSigma x) (varsOfSigma y)
varsOfRho (Rsum x y) = union3 (varsOfSigma x) (varsOfSigma y)
varsOfRho (Rtau x) = varsOfTau x

tvsTau x = fst3(varsOfTau x)


---------------------------------------------------------------
-- Computing most general unifiers. Done in a side effect free way
-- Note that Flexi vars might be bound in the unifer returned.
-- A computational pass can force these to be unified later if
-- necessary. See the function "mutVarSolve" and "mguM"

a = TcTv(Tv 5 (Skol "a") star)
b = TcTv(Tv 6 (Skol "b") star)
c = TcTv(Tv 7 (Skol "c") star)

ps = [ Equality b a, Equality c a]

Left qas = mgu [(b,a),(c,a)]
wsd = subTau qas (tpair a (tpair b c))

mostGenUnify xs =
  case mgu xs of
    Left ans -> return ans
    Right (s,x,y) -> fail s

mgu :: [(Tau,Tau)] -> Either [(TcTv,Tau)] (String,Tau,Tau)
mgu [] = Left []
mgu ((TcTv (Tv n _ _),TcTv (Tv m _ _)):xs) | n==m = mgu xs

mgu ((TcTv (x@(Tv n (Flexi _) _)),tau):xs) = mguVar x tau xs
mgu ((tau,TcTv (x@(Tv n (Flexi _) _))):xs) = mguVar x tau xs

mgu ((TyApp x y,TyApp a b):xs) = mgu ((x,a):(y,b):xs)
mgu ((TyCon sx level_ s1 _,TyCon tx level_2 s2 _):xs) | s1==s2 = mgu xs -- TODO LEVEL
mgu ((Star n,Star m):xs) | n==m = mgu xs
mgu ((Karr x y,Karr a b):xs) = mgu ((x,a):(y,b):xs)
mgu ((x@(TyFun f _ ys),y@(TyFun g _ zs)):xs) =
  if f==g then mgu (zip ys zs ++ xs) else Right("TyFun doesn't match",x,y)
mgu ((x@(TyVar s k),y):xs) = Right("No TyVar in MGU", x, y)
mgu ((y,x@(TyVar s k)):xs) = Right("No TyVar in MGU", x, y)
mgu ((TySyn nm n fs as x,y):xs) = mgu ((x,y):xs)
mgu ((y,TySyn nm n fs as x):xs) = mgu ((y,x):xs)

mgu ((TcTv (x@(Tv n (Rigid _ _ _) _)),tau):xs) = Right("Rigid",TcTv x,tau)
mgu ((tau,TcTv (x@(Tv n (Rigid _ _ _) _))):xs) = Right("Rigid",TcTv x,tau)

mgu ((x,y):xs) = Right("No Match", x, y)


mguVar :: TcTv -> Tau -> [(Tau,Tau)] -> Either [(TcTv,Tau)] ([Char],Tau,Tau)
mguVar x tau xs = if (elem x vs)
                     then Right("occurs check", TcTv x, tau)
                     else compose new2 (Left new1)
  where vs = tvsTau tau
        new1 = [(x,tau)]
        new2 = mgu (subPairs new1 xs)

compose (Left s1) (Left s2) = Left ([(u,subTau s1 t) | (u,t) <- s2] ++ s1)
compose _ (Right x) = Right x
compose (Right y) _ = Right y

o s1 s2 = [(u,subTau s1 t) | (u,t) <- s2] ++ s1

----------------------------------------------------------------------
-- While Matching, One assumes only variables on the left can match
-- And, that such variables never appear on the right.

match :: Monad m => [(TcTv,Tau)] -> [(Tau,Tau)] -> m [(TcTv,Tau)]
match env [] = return env
match env ((TcTv (Tv n _ _),TcTv (Tv m _ _)):xs) | n==m = match env xs
match env ((TcTv (x@(Tv n (Flexi _) _)),tau):xs) = matchVar env x tau xs
match env ((TyApp x y,TyApp a b):xs) = match env ((x,a):(y,b):xs)
match env ((TyCon sx level_ s1 _,TyCon tx level_2 s2 _):xs) | s1==s2 = match env xs -- TODO LEVEL
match env ((Star n,Star m):xs) | n==m = match env xs
match env ((Karr x y,Karr a b):xs) = match env ((x,a):(y,b):xs)
match env ((x@(TyFun f _ ys),y@(TyFun g _ zs)):xs) =
  if f==g then match env (zip ys zs ++ xs) else fail "TyFun doesn't match"
match env ((x@(TyVar s k),y):xs) = fail "No TyVar in match"
match env ((y,x@(TyVar s k)):xs) = fail "No TyVar in match"
match env ((TySyn nm n fs as x,y):xs) = match env ((x,y):xs)
match env ((y,TySyn nm n fs as x):xs) = match env ((y,x):xs)
match env ((x,y):xs) = fail "No Match"

matchVar env x tau xs =
    case find (\ (v,t) -> v==x) env of
      Just (v,t) -> if t==tau then match env xs else fail "Duplicate"
      Nothing -> match ((x,tau):env) xs


--------------------------------------------------------------------

x2 = [(v 843,Star LvZero)
     ,(v 764,Karr (v 843) (v 845))
     ]

v n = TcTv(Tv n (Rigid All Z (show n)) star)
u n = (Tv n (Rigid All Z (show n)) star)


x3 = [(v 2626,f(v 2632,v 2634)),(v 2626,f(v 2642,v 2640))]
 where f (x,y) = tpair x y

test2 :: [(Tau,Tau)]
test2 =
  [(u 843,Star LvZero)
  ,(u 855,tarr (v 851) (v 853))
  ,(u 845,Star LvZero)
  ,(u 857,tarr(TyApp (v 847) (v 851)) (TyApp (v 849) (v 853)))
  ,(u 764,Karr (v 843) (v 845))
  ,(u 766,v 847)
  ,(u 766,v 849)
  ,(u 768,tarr (v 855) (v 857))
  ,(u 764,Karr (Star LvZero) (Star LvZero))
  ,(u 766,listT)]
 where v n = TcTv(Tv n (Rigid All Z (show n)) star)
       u n = v n

go = mgu test2

-------------------------------------------------------------
-- sometimes when debugging, you need to see
-- what constructors are being used to make
-- a type, since the "show" printed version
-- is ambiguous. "sht" allows you to do this.

class Sht t where
  shtt :: t -> String

instance Sht t => Sht (Expected t) where
  shtt (Check t) = shtt t
  shtt (Infer r) = "infer"

instance Sht Tau where
  shtt = sht
instance Sht Rho where
  shtt = shtR
instance Sht Sigma where
  shtt = shtS
instance Sht Pred where
  shtt = shtEq
instance (Sht p,Sht s) => Sht ([p],s) where
  shtt (ps,s) = shtt ps ++ " => "++shtt s
instance Sht x => Sht [x] where
  shtt xs = plistf shtt "[" xs "," "]"
instance Sht Kind where
  shtt (MK s) = shtt s
instance Sht PolyKind where
  shtt (K z) = shtt z


shtP (x,y) = "("++shtt x++"," ++ shtt y++")"

sht (TyVar n k) = "(TyVar "++show n++"::"++shtt k++")"
sht (TyApp x y) = "(TyApp "++sht x++" "++sht y++")"
sht (TyCon sx l x k) = "(Con "++x++"@"++show l++" %"++show sx++")"  --  ++"_"++show l++":"++shtt k++")"
sht (Star n) = "(Star "++show n++")"
sht (Karr x y) = "(Karr "++sht x++" "++sht y++")"
sht (TcTv (Tv n (Flexi _) k))  = "(Flex " ++ show n ++":"++shtt k++")"
sht (TcTv (Tv n (Skol _) k))  = "(Skol " ++ show n ++shtt k++")"
sht (TcTv (Tv n (Rigid _ _ _) k))  =
    "(Rigid " ++ show n ++":"++shtt k++")"
sht (TyFun nm k xs) = "{TyFun ("++nm ++ "::"++shtt k++")"++plistf sht " " xs " " "}"
sht (TySyn nm n fs as t) = "{Syn "++nm++(plistf sht " " as " " " = ")++sht t++"}"
-- sht x = show x

shtR (Rarrow x y) = "("++shtS x++" r-> "++shtR y++")"
shtR (Rpair x y) = "R("++shtS x++","++shtS y++")"
shtR (Rsum x y) = "R("++shtS x++"+"++shtS y++")"
shtR (Rtau x) = "RTau("++sht x++")"

shtS (Forall xs) =
  let (ys,(eqs,rho)) = unsafeUnwind xs
      f [] = ""
      f [(nm,MK k,_)] = "("++show nm++":"++sht k++")"
      f ((nm,MK k,_):xs) = "("++show nm++":"++sht k++")"++"\n  "++f xs
  in "(forall\n  "++(f ys)++ plistf shtEq "(" eqs "," ")"++" => "++shtR rho++")"

shtEq (Equality x y) = "Equality("++sht x++","++sht y++")"
shtEq (Rel ts) = "Rel("++sht ts++")"


-- =============================================================
-- New style Display
-- =============================================================

class NameStore d where
   --useStore :: Kind -> Integer -> (String -> String) -> d -> (d,String)
   useStoreName :: Name -> Kind -> (String -> String) -> d -> (d,String)
   useStoreTcTv :: TcTv -> (String -> String) -> d -> (d,String)

class NameStore d => Exhibit d t where
  exhibit :: d -> t -> (d,String)

instance NameStore d => Exhibit d Integer where
  exhibit d n = (d,show n)

instance NameStore d => Exhibit d (TcTv,Kind) where
  exhibit d (t,MK k) = (d3,a++b)
     where (d2,a) = exhibit d t
           (d3,b) = exhibitKinding d2 k


instance NameStore d => Exhibit d String where
  exhibit d s = (d,s)

exhibit2 xs1 (x,y) = (xs3,sx,sy)
  where (xs2,sx) = exhibit xs1 x
        (xs3,sy) = exhibit xs2 y

exhibit3 xs1 (x,y,z) = (xs4,sx,sy,sz)
  where (xs2,sx) = exhibit xs1 x
        (xs3,sy) = exhibit xs2 y
        (xs4,sz) = exhibit xs3 z

--instance (NameStore d,Exhibit d a,Exhibit d b, Exhibit d c) => Exhibit d (a,b,c) where
--  exhibit d x = (d,a++b++c) where (d,a,b,c) = exhibit3 d x

-----------------------------------------------------
-- Helper functions

-- exhibit a list, given a function to exhibit an element
exhibitL :: (a -> b -> (a,[Char])) -> a -> [b] -> [Char] -> (a,[Char])
exhibitL = dispL

-- Put parenthesis around Tau's that need them

exhibitpar :: Exhibit a Tau => a -> Tau -> (a,String)
exhibitpar xs z@(TyApp (TyCon sx _ "[]" _) x) = exhibit xs z
exhibitpar xs z@(TyApp (TyApp (TyCon sx _ "(,)" _) x) y) = exhibit xs z
exhibitpar xs z@(TyApp (TyApp (TyCon sx _ "(+)" _) x) y) = exhibit xs z
exhibitpar xs z@(TyApp (TyApp (TyCon (Lx _) _ _ _) _) _) = exhibit xs z
exhibitpar xs z@(TyApp (TyApp (TyCon (Px _) _ _ _) _) _) = exhibit xs z
exhibitpar xs z@(TyApp (TyCon (Nx _) _ _ _) _) = exhibit xs z
exhibitpar xs  z | isRow z = exhibit xs z
exhibitpar xs x@(Karr _ _) = (ys,"("++ ans ++ ")")
  where (ys,ans) = exhibit xs x
exhibitpar xs x@(TyApp _ _) = (ys,"("++ans++ ")")
  where (ys,ans) = exhibit xs x
exhibitpar xs x@(TySyn nm n fs as t) | n>1 =  (ys,"("++ans++ ")")
  where (ys,ans) = exhibit xs x
exhibitpar xs x@(TyEx _) = (ys,"("++ ans ++ ")")
  where (ys,ans) = exhibit xs x
exhibitpar xs x = exhibit xs x

-- exhibit a TcTv
exhibitTv :: NameStore a => a -> TcTv -> (a,String)
exhibitTv d1 (x@(Tv _ flav _)) = useStoreTcTv x (tVarPrefix flav) d1

tVarPrefix (Flexi _) n = n
tVarPrefix (Rigid _ _ _) n = "_"++n
tVarPrefix (Skol _) n = "!"++n

instance NameStore d => Exhibit d TcTv where
  exhibit = exhibitTv


-- exhibit an arrow type at the Tau level
exhibitArr :: Exhibit a Tau => a -> Tau -> (a,[Char])
exhibitArr xs (t@(TyApp (TyApp (TyCon sx _ "(->)" _) x) y)) = (ys,"("++z++")")
  where (ys,z) = exhibit xs t
exhibitArr xs (t@(Karr _ _)) = (ys,"("++z++")")
  where (ys,z) = exhibit xs t
exhibitArr xs x@(TyEx _) = (ys,"("++ ans ++ ")")
  where (ys,ans) = exhibit xs x
exhibitArr xs t = exhibit xs t

-- exhibit an arrow type at the Rho level
exhibitRarr xs (t@(Forall (Cons _ _))) = (ys,"("++z++")")
  where (ys,z) = exhibit xs t
exhibitRarr xs (t@(Forall (Nil (_,Rtau (TyApp (TyApp (TyCon sx _ "(->)" _) x) y))))) = (ys,"("++z++")")
  where (ys,z) = exhibit xs t
exhibitRarr xs t = exhibit xs t


--  returns things like  Nat:*1, Row:(*1 ~> *1):*2
exhibitKinding :: NameStore a => a -> Tau -> (a,[Char])
exhibitKinding d1 (Star LvZero) = (d1,":*0")
exhibitKinding d1 (t@(Star n)) = (d1,":*"++show n)
exhibitKinding d1 (TyVar nm (MK k)) = (d3,":"++nmStr++kStr)
   where (d2,nmStr) = useStoreName nm (MK k) f d1 where f s = "'"++s
         (d3,kStr) = exhibitKinding d2 k
exhibitKinding d1 (TcTv (v@(Tv _ _ (MK k)))) = (d3,":"++nmStr++kStr)
   where (d2,nmStr) = exhibitTv d1 v
         (d3,kStr) = exhibitKinding d2 k
exhibitKinding d1 (TyCon sx (LvSucc LvZero) s k) = (d1,":"++s)
exhibitKinding d1 (TyCon sx l s k) = (d1,{- "_"++show l++ -} ":"++s)
exhibitKinding d1 (x@(Karr _ _)) = (d2,":"++s) where (d2,s)= exhibit d1 x
exhibitKinding d1 (x@(TyApp _ _)) = (d2,":"++s) where (d2,s)= exhibit d1 x
exhibitKinding d1 x = (d1,":"++show x)


exhibitLdata quant d1 args =  (d4,prefix ++ eqsS ++ rhoS)
    where (trips,(eqs,rho)) = unsafeUnwind args
          (d2,prefix) = tripf d1 trips
          (d3,eqsS) = feqs d2 eqs
          (d4,rhoS) = exhibit d3 rho
          sh All = "forall "
          sh Ex  = "exists "
          feqs d [] = (d,"")
          feqs d [x::Pred] = (d1,s++" => ") where (d1,s) = exhibit d x
          feqs d xs = (d1,"("++s++") => ") where (d1,s) = exhibitL exhibit d xs ","
          tripf d1 [] = (d1,"")
          tripf d1 trips = (d2,sh quant++argsStr ++ ".")
            where (d2,argsStr) = exhibitL pp d1 trips " "
          pp d2 (nm,MK k,q) =
            let (d3,name) = useStoreName nm (MK k) (prefix k) d2
                prefix (TcTv (Tv _ (Skol _) _)) s = (case q of {Ex -> "!"; All -> ""})++s
                prefix _ s = (case q of {Ex -> "_"; All -> ""})++s
            in case k of
                (Star LvZero) -> (d3,name)
                _ -> let (d4,kind) = exhibitKinding d3 k
                     in (d4,"("++name ++ kind++")")



---------------------------------------------------------------
-- Now some instances for exhibiting different type like things
-- All these are paramterized by "d" being a NameStore

instance NameStore d => Exhibit d Int where
  exhibit d n = (d,show n)

instance Exhibit (DispInfo Z) Bool where
  exhibit d n = (d,show n)


-- Kind
instance NameStore d => Exhibit d Kind where
  exhibit d1 (MK k) = exhibit d1 k


-----------------------------------------------
-- Exhibiting Syntactic Extensions in Tau types
prescript "" = ""
prescript _ = "#"
postscript "" = ""
postscript a = a

exSynNat d (TyApp (TyCon (Nx(key,zero,succ)) _ c k) x)| succ == c = f d 1 x
  where f d n (TyCon (Nx(key,zero,succ)) _ c k)| zero == c = (d,"#"++show n++ postscript key)
        f d n (TyApp (TyCon (Nx(key,zero,succ)) _ c k) x)| succ == c = f d (n+1) x
        f d n v = let (d2,ans) = exhibit d v
                  in (d2,"#("++show n++"+"++ans++ ")" ++ postscript key)
exSynNat d v = (d,"Ill-formed Natural number extension: "++shtt v)

exSynList d (t@(TyApp (TyApp (TyCon (Lx(key,_,cons)) _ c1 _) x) y))
    | c1==cons =(d2,prescript key ++ "[" ++ ans ++ "]"++postscript key)
  where (d2,ans) = f d t
        f d (TyCon (Lx(key,nil,cons)) _ c k)| nil == c = (d,"")
        {-
        f d (TyApp (TyApp (TyCon (Lx(key,_,cons)) _ c1 _) x)
                   (TyCon (Lx(_,nil,_)) _ c2 _)) | c1==cons && c2==nil
                   = exhibit d x
        -}
        f d (TyApp (TyApp (TyCon (Lx(key,_,cons)) _ c1 _) x) y)| c1==cons =
          case y of
           (TyCon (Lx(_,nil,_)) _ c2 _) | c2==nil -> exhibit d x
           (TyApp (TyApp (TyCon (Lx(key,_,cons)) _ c1 _) _) _)| c1==cons -> (d2,ans)
             where (d1,elem) = exhibit d x
                   (d2,tail) = f d1 y
                   ans = elem ++ "," ++ tail
           other -> (d2,elem++"; "++ans)
             where (d1,elem) = exhibit d x
                   (d2,ans) = exhibit d1 other
        f d t = (d2,"; "++ans) where (d2,ans) = exhibit d t
exSynList d t = (d,"2Ill-formed List extension: "++sht t)

exSynPair d (t@(TyApp (TyApp (TyCon (Px(key,pair)) _ c1 _) x) y))
    | c1==pair =(d2,prescript key ++ "(" ++ x' ++","++ y' ++ ")"++postscript key)
  where (d1,x') = exhibit d x
        (d2,y') = exhibit d1 y

-- Tau
instance NameStore d => Exhibit d Tau where
  exhibit xs (t@(TyCon (Nx(k,z,s)) _ c _)) | c==z = (xs,"#0" ++ postscript k)
  exhibit xs (t@(TyCon (Lx(k,n,c)) _ s _)) | s==n = (xs,prescript k++"[]"++postscript k)
  exhibit xs (t@(TyApp (TyApp (TyCon (Lx _) _ _ _) _) _)) = exSynList xs t
  exhibit xs (t@(TyApp (TyApp (TyCon (Px _) _ _ _) _) _)) = exSynPair xs t
  exhibit xs (t@(TyApp (TyCon (Nx _) _ _ _) x)) = exSynNat xs t
  exhibit xs (t@(TyCon sx (LvSucc LvZero) s k)) = (xs,s)
  exhibit xs (t@(TyCon _ l s k)) = (xs,s {- ++"_"++show l -} )
  --exhibit xs (t@(TyCon sx l s k)) = (xs,s++"%"++synKey sx {- ++"_"++show l -} )
  exhibit e (tau@(TyApp x y)) | isRow tau =
    case rowElem tau [] of
      Left xs -> let (e2,mid) = exhibitL exhibit e xs ","
                 in (e2,"{"++mid++"}")
      Right(xs,dot) ->
        let (e2,mid) = exhibitL exhibit e xs ","
            (e3,end) = exhibit e2 dot
        in (e3,"{"++mid++"; "++end++"}")
  exhibit e (TyApp (TyApp (TyCon sx _ "Has" _) x) y) = (e2,x1 ++":"++y1)
    where (e1,x1) = exhibit e x
          (e2,y1) = exhibit e1 y
  exhibit e (TyApp (TyCon sx _ "[]" _) x) = (ys,"[" ++ ans ++ "]")
    where (ys,ans) = exhibit e x
  exhibit e (TyApp (TyApp (TyCon sx _ "(,)" _) x) y) = (zs,"(" ++ a ++ ","++ b++")")
    where (ys,a) = exhibit e x
          (zs,b) = exhibit ys y
  exhibit e (TyApp (TyApp (TyCon sx _ "(->)" _) x) y) = (zs,a ++ " -> "++ b)
    where (ys,a) = exhibitArr e x
          (zs,b) = exhibit ys y
  exhibit e (TyApp (TyApp (TyCon sx _ "(+)" _) x) y) = (zs,"(" ++ a ++ "+"++ b ++")")
    where (ys,a) = exhibitpar e x
          (zs,b) = exhibitpar ys y
  exhibit xs (TyApp x y) = (zs,a++" "++b)
    where (ys,a) = exhibit xs x
          (zs,b) = exhibitpar ys y
  exhibit xs (Star LvZero) = (xs,"*0")
  exhibit xs (Star n) = (xs,"*"++show n)
  exhibit xs (TyVar nm k) = useStoreName nm k f xs -- (zs,"("++ans++":: "++k2++")")
    where f s = "'"++s
          (ys,ans) = useStoreName nm k f xs
          (zs,k2) = exhibit ys k
  exhibit xs (Karr x y) = (zs,a ++ " ~> "++ b)
    where (ys,a) = exhibitArr xs x
          (zs,b) = exhibit ys y
  exhibit info (TcTv v) =  exhibitTv info v
  exhibit info (TyFun f k xs) = (d2,"{"++f++" "++body++"}")
    where (d2,body) = exhibitL exhibitpar info xs " "
  exhibit info (TySyn nm n fs as t) = (d2,nm++" "++xs)
    where (d2,xs) = exhibitL exhibit info as " "
  exhibit xs (TyEx x) = exhibitLdata Ex xs x

-- Rho
instance NameStore d => Exhibit d Rho where
  exhibit xs (Rtau x) = exhibit xs x
  exhibit xs (Rarrow x y) = (zs,a++" -> "++b)
    where (ys,a) = exhibitRarr xs x
          (zs,b) = exhibit ys y
  exhibit xs (Rpair x y) = (zs,"("++a++","++b++")")
    where (ys,a) = exhibit xs x
          (zs,b) = exhibit ys y
  exhibit xs (Rsum x y) = (zs,"("++a++"+"++b++")")
    where (ys,a) = exhibit xs x
          (zs,b) = exhibit ys y

instance (NameStore d,Exhibit d x) => Exhibit d (Expected x) where
  exhibit d1 (Check x) = exhibit d1 x
  exhibit d1 (Infer _) =(d1,"Infer Reference")

-- Sigma
instance NameStore d => Exhibit d Sigma where
  exhibit d1 (Forall args) = exhibitLdata All d1 args

-- PolyKind
instance NameStore d => Exhibit d PolyKind where
  exhibit d1 (K(Forall args)) = exhibitLdata All d1 args

-- [(Tau,Tau)]
instance NameStore d => Exhibit d [(Tau,Tau)] where
  exhibit xs [] = (xs,"")
  exhibit xs ys = (zs,"("++ans++") => ")
    where (zs,ans) = exhibitL exhibit xs ys ", "

-- Pred
instance NameStore d => Exhibit d Pred where
  exhibit xs (Rel ts) = let (a,b) = exhibit xs ts in (a,b)
  exhibit xs (Equality x y) = (zs,"Equal "++a++" "++b)
    where (ys,a) = exhibitpar xs x
          (zs,b) = exhibitpar ys y

-- [Pred]
instance NameStore d => Exhibit d [Pred] where
  exhibit xs [] = (xs,"")
  exhibit xs ys = exhibitL exhibit xs ys ", "

instance NameStore d => Exhibit d [PPred] where
  exhibit xs [] = (xs,"")
  exhibit xs ys = exhibitL exhibit xs ys ", "

instance NameStore d => Exhibit d [(TcTv,Tau)] where
  exhibit d ys = (d1,"{"++s++"}")
    where (d1,s) = f d ys
          f xs [] = (xs,"")
          f xs ys = exhibitL exhibit xs ys ", "


instance NameStore d => Exhibit d (Tau,[(TcTv,Tau)]) where
  exhibit xs (x,y) = (zs,a++" where "++b)
      where (ys,a) = exhibit xs x
            (zs,b) = exhibit ys y

instance NameStore d => Exhibit d (Tau,Tau) where
  exhibit xs (x,y) = (zs,a++"="++b)
    where (ys,a) = exhibit xs x
          (zs,b) = exhibit ys y


instance NameStore d => Exhibit d (TcTv,Tau) where
  exhibit xs (x,y) = (zs,a++"="++b)
    where (ys,a) = exhibitTv xs x
          (zs,b) = exhibit ys y

instance Exhibit d x => Exhibit d (Maybe x) where
  exhibit d Nothing = (d,"Nothing")
  exhibit d (Just x) = (d1,"(Just "++s++")") where (d1,s) = exhibit d x

{-
instance NameStore d => Exhibit d ([Pred], Rho) where
  exhibit xs (es,r) = (ys,esx ++ " => " ++ rx)
     where (ys,esx,rx) = exhibit2 xs (es,r)
-}

instance (NameStore d,Exhibit d a) => Exhibit d ([Pred], a) where
  exhibit xs (es,r) = (ys,esx ++ " => " ++ rx)
     where (ys,esx,rx) = exhibit2 xs (es,r)


instance NameStore d => Exhibit d (Name,Kind,Quant) where
  exhibit xs (nm,k,q) = (d2,"("++nmS++","++kS++","++show q++")")
    where (d1,nmS) = useStoreName nm k f xs
          (d2,kS) = exhibit d1 k
          f s = "'"++s

instance NameStore d => Exhibit d (String,Tau,PolyKind) where
  exhibit xs (str,tau,pkind)= (d2,"("++str++","++tauS++","++pkindS++")")
    where (d1,tauS) = exhibit xs tau
          (d2,pkindS) = exhibit d1 pkind

instance NameStore d => Exhibit d (String,PT,Quant) where
  exhibit xs (str,pt,q)= (d1,"("++str++","++tauS++","++show q++")")
    where (d1,tauS) = exhibit xs pt


------------------------------------------------
-- Make Display instances

instance NameStore (DispInfo Z) where
  --useStore k = useDisplay
  useStoreName name kind newname d = useDisplay newname d (ZVar name kind)
  useStoreTcTv v@(Tv uniq flavor kind) f d = useDisplay f d (ZTv v)

instance Exhibit (DispInfo Z) t => Display t Z where
  disp = exhibit

-------------------------------------------------
-- Make Alpha instances

class Alpha t where
  alpha :: [(Name,String)] -> t -> String

instance Exhibit [(Name,String)] t => Alpha t where
  alpha disp x = y where (disp2,y) = exhibit disp x

instance NameStore [(Name,String)] where
  useStoreTcTv v f xs = (xs,show v)
  useStoreName nm k f xs = case lookup nm xs of
                       Just s -> (xs,s)
                       Nothing -> ((nm,new):xs,new)
    where new = f(first xs (choices k))
          first old (x:xs) = if find x old then first old xs else x
          find x [] = False
          find x ((_,y):old) = if x==y then True else find x old
          --nm = integer2Name i

-- Select an infinite list of possible choices given a Kind
choices :: Kind -> [String]
choices k = case k of
    (MK (Star LvZero))                      -> typesCh
    (MK (Karr (Star LvZero) (Star LvZero))) -> typeConstrsCh
    (MK (Star (LvSucc LvZero)))       -> kindsCh
    (MK (Karr _ _))                   -> higherOrderCh
    _                                 -> otherCh

typesCh       = makeNames "abcde"   -- *
typeConstrsCh = makeNames "ts"      -- (* -1-> *)
kindsCh       = makeNames "k"       -- *1
higherOrderCh = makeNames "fgh"     -- (k -> k)
otherCh       = makeNames "uvwxyz"  -- other

pprint :: Exhibit (DispInfo Z) b => b -> [Char]
pprint x = s
 where (d2,s) = exhibit (disp0:: DispInfo Z) x

------------------------------------------------------------
-- Turn types into PT inorder to render them with indentation

toPT :: Exhibit a Tau => a -> Tau -> (a,PT)
toPT d (TyVar nm k) = (d2,TyVar' s) where (d2,s) = useStoreName nm k ("'"++) d
toPT d (TyApp (TyApp (TyCon sx n "(->)" k) x) y) = (d2,Rarrow' a b)
  where (d1,a) = toPT d x
        (d2,b) = toPT d1 y
toPT d (TyApp x y) = (d2,TyApp' a b)
  where (d1,a) = toPT d x
        (d2,b) = toPT d1 y
toPT d (TyCon sx l s k) = (d,TyCon' s)
toPT d (Star n) =
  case fromLevel n of
    Just m -> (d,Star' m)
    Nothing -> (d,TyVar' (show n))
toPT d (Karr x y) = (d2,Karrow' a b)
  where (d1,a) = toPT d x
        (d2,b) = toPT d1 y
toPT d (TyFun nm k args) = (d1,TyFun' ((TyVar' nm):ys))
  where (d1,ys) = toL toPT d args
toPT d (TcTv v) = (d2,TyVar' s) where (d2,s) = exhibitTv d v
toPT d (TySyn nm n formal actual def) = (d2,foldl1 TyApp' (TyVar' nm : ys))
  where (d2,ys) = toL toPT d actual
toPT d (TyEx ys) = (dn,Forallx Ex vs preds body)
  where (args,(ps,tau)) = unsafeUnwind ys
        (d1,body) = toPT d tau
        (d2,preds) = toL toPPred d1 ps
        (dn,vs) = toL toTrip d2 args

toPPred d (Equality x y) = (d2,Equality' a b)
  where (d1,a) = toPT d x
        (d2,b) = toPT d1 y
toPPred d (Rel x) = (d1,Rel' "" a) where (d1,a) = toPT d x

toTrip d (nm,MK k,q) = (d2,(s,a,q))
   where (d1,s) = useStoreName nm (MK k) ("'"++) d
         (d2,a) = toPT d1 k

toL f d [] = (d,[])
toL f d (x:xs) = (d2,y:ys)
  where (d1,y) = f d x
        (d2,ys) = toL f d1 xs

rho2PT d (Rarrow x y) = (d2,Rarrow' a b)
  where (d1,a) = sigma2PT d x
        (d2,b) = rho2PT d1 y
rho2PT d (Rsum x y) = (d2,(TyApp' (TyApp' (TyCon' "(,)") a) b))
  where (d1,a) = sigma2PT d x
        (d2,b) = sigma2PT d1 y
rho2PT d (Rpair x y) = (d2,(TyApp' (TyApp' (TyCon' "(+)") a) b))
  where (d1,a) = sigma2PT d x
        (d2,b) = sigma2PT d1 y
rho2PT d (Rtau x) = toPT d x

sigma2PT d (Forall ys) = (dn,Forallx All vs preds body)
  where (args,(ps,tau)) = unsafeUnwind ys
        (d1,body) = rho2PT d tau
        (d2,preds) = toL toPPred d1 ps
        (dn,vs) = toL toTrip d2 args

------------------------------------------------------------
-- Make Show instances

instance Show Tau where
  show x = y where (disp2,y) = exhibit () x

instance Show Rho where
  show x = y where (disp2,y) = exhibit () x

instance Show Sigma  where
  show x = y where (disp2,y) = exhibit () x

instance Show Kind  where
  show x = y where (disp2,y) = exhibit () x

instance Show PolyKind  where
  show x = y where (disp2,y) = exhibit () x

instance Show Pred  where
  show x = y where (disp2,y) = exhibit () x

instance Show a => Show (Expected a) where
  show (Check a) = "(Check "++show a++")"
  show (Infer ref) = "Infer"

instance Show PPred where
  show x = y where (disp2,y) = exhibit () x

instance Show TcTv where
  show (Tv unq (flav@(Flexi _)) k) = "z"++tVarPrefix flav (show unq)
  show (Tv unq flav k) = tVarPrefix flav (show unq)

instance NameStore () where
  useStoreTcTv v f xs = (xs,show v)
  useStoreName nm k f xs = (xs,show nm)

------------------------------------------------------

solveHP ::  TyCh m => (String,Rho) -> [Pred] -> [Pred] -> m ([Pred],[(TcTv,Tau)])
solveHP context@(s,r) truths oblig =
  do { truths2 <- zonk truths
     ; oblig2 <- zonk oblig
     ; let (hotruths,fots) = span higherOrder truths2
           counts = map (countM oblig2) hotruths
           force (1,u) = mutVarSolve u
           force (n,u) = return []
     ; mapM force counts
     ; truths3 <- zonk truths2
     ; oblig3 <- zonk oblig2
     -- ; warn [Ds "Calling Solve inside solveHP ",Dd oblig3]
     ; setTruths truths3 (solveSomeEqs ("3."++s,r) oblig3)
     }


-- When we map "matchRel p" over a list we get a list of (count,unifier).
-- Interpret this as (1,unifer) if "p"  matches and (0,[]) if it doesn't.
-- "sumM"ing up such a list we get (number_of_matches,first_unifier)
-- if it is (1,unifer) then there was exactly 1 match and unifer
-- comes from that match. For those with exactly 1 match, we can force
-- the unification to take place, by using solveMutVars.

sumM :: [(Int,[a])] -> (Int,[a])
sumM [] = (0,[])
sumM ((n,xs):zs) = (n+m,xs) where (m,_) = sumM zs

matchRel (Rel p) (Rel q) =
  case mgu [(p,q)] of
    Left u -> (1,u)
    Right (a,b,c) -> (0,[])
matchRel p q = (0,[])

countM ps p = sumM(map (matchRel p) ps)

higherOrder (Rel t) = ho t
  where ho (TyApp f y) = ho f
        ho (TyCon sx l nm k) = False
        ho (TcTv _) = True
        ho _ = False
higherOrder _ = False

------------------------------------------------------
test12 = (TcTv a1,f)
 where a1 = testflex 0
       f = TyFun "plus" pk [TcTv a1,TyCon Ox LvZero "Z" pk]
       pk = poly (MK natT)

-------------------------------------------------------
-------------------------------------------------------
-- Split a list of Predicates into 1 of four classes
-- 1) Equality  that are Mutvar solvable,
-- 2) Equalities that are Easy narrowing (it looks easy at least),
-- 3) Equalities that are hard to narrow
-- 4) Other kinds of predicates.
--
-- 1) Mutvar solvalble look like (Equal x type),
-- where on side is a variable, except where x = skol
-- or y={plus y z}, ie. a TyFun where the var (y) occurs
-- in the other side, like the y in  {plus y z}.
--
-- 2) Easy ones include  (Equal Z {plus n n}) where one
-- side is a ground term. They look easy, but they might be hard.
-- One can't tell without trying, but it is worth trying.
--
-- 3) Hard is all other equalites like (Equal x {plus a b})
-- or {Equal {plus Z a} {plus a b}), or any other predicate.
--
-- 4) Other predicates like (Rel x) etc.

data HardClass = MutSolve | Easy | Hard

rootT (TyApp f y) ys = rootT f (y:ys)
rootT (TyCon sx level nm k) ys = return(sx,level,nm,k,ys)
rootT _ _ = fail "Not an application of a TyCon"

rootTau (TyApp a b) ts = rootTau a (b:ts)
rootTau f ts = (f,ts)

groundTerm (TyVar n k) = False
groundTerm t@(TyApp x y) =
  case rootT t [] of
   Just(sx,lev,nm,k,xs) -> all groundTerm xs
   Nothing -> False
groundTerm x@(Star n) = True
groundTerm (Karr a b) = all groundTerm [a,b]
groundTerm (TyFun s p xs) = False
groundTerm (TcTv s) = False
groundTerm (TySyn s n xy ys t) = groundTerm t
groundTerm x@(TyEx _) = False
groundTerm (TyCon sx level_ n k) = True

fst3 (x,y,z) = x

splitClass (TcTv (Tv un (Skol _) k)) any = Hard
splitClass any (TcTv (Tv un (Skol _) k)) = Hard
splitClass (TcTv x) (y@(TyFun _ _ _)) | all (/=x) (fst3 (varsOfTau y)) = MutSolve
splitClass (y@(TyFun _ _ _)) (TcTv x) | all (/=x) (fst3 (varsOfTau y)) = MutSolve
splitClass (TcTv x) any = MutSolve
splitClass any (TcTv x) = MutSolve
splitClass _ _ = Hard

splitV [] (os,hs,es,ms) = (os,hs,es,ms)
splitV ((p@(Equality x y)):zs) (os,hs,es,ms) =
   case (splitClass x y,x,y) of
     (Hard,_,_) -> splitV zs (os,p:hs,es,ms)
     (MutSolve,TcTv v,tau) -> splitV zs (os,hs,es,(v,tau):ms)
     (MutSolve,tau,TcTv v) -> splitV zs (os,hs,es,(v,tau):ms)
splitV ((p@(Rel _)):zs) (os,hs,es,ms) = splitV zs (p:os,hs,es,ms)
-- splitV (p:zs) (os,hs,es,ms) = splitV zs (os,p:hs,es,ms)

-- it is an invariant that
-- Hard is all Equality
-- Easy is all EqAssump
-- MutSolve is (TvTc,tau)
-- other is anything

splitByClass ps = splitV ps ([],[],[],[])

instance Sht TcTv where
  shtt v = sht (TcTv v)
instance Sht (TcTv,Tau) where
  shtt (x,y) = "("++shtt x++","++shtt y++")"


apply_mutVarSolve_ToSomeEqPreds preds =
  do { let (other,hard,easy,mutSolve) = splitByClass preds
     ; unifier <- mutVarSolve mutSolve
     ; mm <- zonk mutSolve
     ; hard2 <- sub ([],unifier,[],[]) hard -- TODO LEVEL
     ; easy2 <- sub ([],unifier,[],[]) easy
     ; other2 <- sub ([],unifier,[],[]) other
     ; return(other2,hard2,easy2,unifier)}

-- To add a list of bindings to the mutable unifier, run down
-- the list overwriting the ref cells for each mutable type var.
-- we use unify (rather than unifyVar) because unification in
-- earlier parts of the list may have overwritten a var further
-- down the list, thus it needs to be zonked, before overwriting.


tryUnify x y = handleM 2 ((unify (TcTv x) y)>> return Nothing)
   (\ message ->
          do { x' <- zonk (TcTv x)
             ; y' <- zonk y
             ; case (x',y') of
                (TcTv v,tau) -> return(Just(v,tau))
                (tau,TcTv v) -> return(Just(v,tau))
                other -> failM 2 [Ds message]})

------------------------------------------------------------------
-- Once we have tried all possible backtracking, there comes a
-- point where me must incorporate the single solution into
-- the mutable state unifier. This is done by mguM,
-- this occurs in the TyCh monad.

mutVarSolve [] = return []
mutVarSolve ((v@(Tv unq (Flexi _) k),tau):more) =
  maybeM (tryUnify v tau)  -- Always bind this way first
         (\ p -> do { ps <- mutVarSolve more; return(p:ps) })
         (mutVarSolve more)
mutVarSolve ((x,TcTv(v@(Tv unq (Flexi _) k))):more) =
  maybeM (tryUnify v (TcTv x))    -- Use this case only if case above doesn't match
         (\ p -> do { ps <- mutVarSolve more; return(p:ps) })
         (mutVarSolve more)
mutVarSolve ((x@(v,tau)):xs) =
  do { ys <- mutVarSolve xs
     ; if (TcTv v)==tau || elem (v,tau) ys
          then return ys
          else return(x:ys) }


-- When we open a (forall vs . ps => r) we want to apply the
-- Equalities in ps that are simply a unifier to "r".

ds s x = Dr [Ds ("\n"++s++" "),Dd x]

normalizeEqn eqns r =
  do { (other,hard,easy,unifier) <- apply_mutVarSolve_ToSomeEqPreds eqns
     ; r2 <- zonk r
     ; let env = ([],unifier,[],[]) -- TODO LEVEL
     ; r2 <- zonk r
     ; r3 <- sub env r2
     ; let g (v,tau) = Equality (TcTv v) tau
     ; return(map g unifier,other++hard++easy,r3)}

--------------------------------------------------------
-- The mguStar invariant is that all terms being unified
-- are completely Rigid, i.e. if they contain variables
-- they are all Rigid flavor variables.

composeStar (Left(s1,eqs)) s2 = Left ([(u,subTau s1 t) | (u,t) <- s2] ++ s1,subPred s2 eqs)
composeStar (Right y) _ = Right y

compStar (Left(s1,eqs1)) (Left(s2,eqs2)) =
  Left([(u,subTau s1 t) | (u,t) <- s2] ++ s1, eqs1 ++ subPred s1 eqs2)
compStar (Left _) (Right y) = Right y
compStar (Right y) _ = Right y

emitStar (x,y) (Left(sub,eqs)) = Left(sub,Equality x y :eqs)
emitStar pair (Right x) = Right x

mguStarVar beta x tau xs =
  do { let vs = tvsTau tau
           new1 = [(x,tau)]
     ; new2 <- mguStar beta (subPairs new1 xs)
     ; return(if (elem x vs)
                 then Right("occurs check", TcTv x, tau)
                 else composeStar new2 new1)}

mguStar:: TyCh m => [TcTv] -> [(Tau,Tau)] -> m(Either ([(TcTv,Tau)],[Pred]) (String,Tau,Tau))
mguStar beta [] = return(Left ([],[]))
mguStar beta ((TcTv (Tv n _ _),TcTv (Tv m _ _)):xs) | n==m
   = mguStar beta xs
mguStar beta ((TcTv a,TcTv b):xs) | elem a beta && not(elem b beta)
   = mguStarVar beta a (TcTv b) xs
mguStar beta ((TcTv b,TcTv a):xs) | elem a beta && not(elem b beta)
   = mguStarVar beta a (TcTv b) xs
mguStar beta ((TcTv (a@(Tv _ _ k)),TcTv b):xs)
   | (elem a beta && elem b beta) || (not(elem a beta) && not(elem b beta))
   = do { loc <- currentLoc
        ; cVar <- newRigidTyVar All loc "CommonVar" k
        ; let c = TcTv cVar
        ; let new1 = [(a,c),(b,c)]
        ; new2 <- mguStar beta (subPairs new1 xs)
        ; return(composeStar new2 new1)}
mguStar beta ((TcTv a,tau):xs) = mguStarVar beta a tau xs
mguStar beta ((tau,TcTv a):xs) = mguStarVar beta a tau xs
mguStar beta ((TyApp x y,TyApp a b):xs) = mguStar beta ((x,a):(y,b):xs)
mguStar beta ((TyCon sx level_ s1 _,TyCon tx level_2 s2 _):xs) | s1==s2 = mguStar beta xs -- TODO LEVEL
mguStar beta ((Star n,Star m):xs) | n==m = mguStar beta xs
mguStar beta ((Karr x y,Karr a b):xs) = mguStar beta ((x,a):(y,b):xs)
mguStar beta ((TySyn nm n fs as x,y):xs) = mguStar beta ((x,y):xs)
mguStar beta ((y,TySyn nm n fs as x):xs) = mguStar beta ((y,x):xs)
mguStar beta ((x@(TyFun f _ ys),y):xs) =
   do { ans <-  (mguStar beta xs); return (emitStar (x,y) ans) }
mguStar beta ((y,x@(TyFun f _ ys)):xs) =
   do { ans <-  (mguStar beta xs); return (emitStar (y,x) ans) }
mguStar beta ((x,y):xs) = return(Right("No Match", x, y))

rigidInstance :: TyCh m => String -> Sigma -> m([TcTv],[Pred],Rho)
rigidInstance s sigma = do { loc <- currentLoc; unBindWith (newRigid loc s) sigma }

existsInstance s sigma = do { loc <- currentLoc; unBindWith (new loc) sigma }
  where new loc name Ex k = newRigid loc s name Ex k
        new loc name All k = newflexi name All k

rigidInstanceL s zs =
 do { loc <- currentLoc; unBindWithL (newRigid loc s) zs }

morepolySS:: TyCh m => [TcTv] -> Sigma -> Sigma -> m(Either ([(TcTv,Tau)],[Pred]) (String,Tau,Tau))
morepolySS beta sigma1 sigma2 =
  do { (skol_tvs,truths,rho) <- rigidInstance (show sigma2) sigma2
     -- we should assume the truths in the next step, not sure how to do this
     ; eitherAns <- morepolySR beta sigma1 rho
     ; (tv1, level_) <- get_tvs sigma1   -- TODO LEVEL
     ; (tv2, level_) <- get_tvs sigma2   -- TODO LEVEL
     ; case eitherAns of
        Right y -> return (Right y)
        Left(sub,ps) ->
            do { (tv3, level_) <- get_tvs ps -- TODO LEVEL
               ; let esc_tvs = tv1++tv2++tv3
                     bad_tvs = filter (`elem` esc_tvs) skol_tvs
               ; case bad_tvs of
                   [] -> return(Left(sub,ps))
                   zs -> return(Right("escapes",string2Tau (show sigma1),string2Tau (show sigma2)))}
     }


string2Tau s = TyCon Ox (lv 0) s (K(simpleSigma (Star LvZero)))


morepolySR:: TyCh m => [TcTv] -> Sigma -> Rho -> m(Either ([(TcTv,Tau)],[Pred]) (String,Tau,Tau))
morepolySR beta (Forall(Nil([],rho1))) rho2 = morepolyRR beta rho1 rho2
morepolySR beta sigma1 rho2 =
     do { (vs,preds,rho1) <- rigidInstance (show sigma1) sigma1 -- instanL sig
        -- generally we instantiate with Flexi vars, but since this
        -- will be passed to mguStar which demands Rigid vars everywhere
        -- we instantiate with Rigid vars. We add vs to Beta since we
        -- want these variables to be eliminated.
        ; eitherAns <- morepolyRR (vs++beta) rho1 rho2
        ; case eitherAns of
           Right y -> return(Right y)
           Left (sub,ps) -> return(Left(sub,ps ++ subPred sub preds))}

thenStar x y = do { a <- x; b <- y; return(compStar a b)}

morepolyRR:: TyCh m => [TcTv] -> Rho -> Rho -> m(Either ([(TcTv,Tau)],[Pred]) (String,Tau,Tau))
morepolyRR s x y = f x y where
  f (Rarrow a b) x = do{(m,n) <- unifyFun x; (morepolyRR s b n) `thenStar` (morepolySS s m a) }
  f x (Rarrow m n) = do{(a,b) <- unifyFun x; (morepolyRR s b n) `thenStar` (morepolySS s m a) }
  f (Rpair m n) (Rpair a b) = morepolySS s m a `thenStar` morepolySS s n b
  f (Rpair m n) x = do{(a,b) <- checkPair x; morepolySS s m a `thenStar` morepolySS s n b}
  f x (Rpair a b) = do{(m,n) <- checkPair x; morepolySS s m a `thenStar` morepolySS s n b}
  f (Rsum m n) (Rsum a b) = morepolySS s m a `thenStar`  morepolySS s n b
  f (Rsum m n) x = do{(a,b) <- checkSum x; morepolySS s m a `thenStar` morepolySS s n b}
  f x (Rsum a b) = do{(m,n) <- checkSum x; morepolySS s m a `thenStar` morepolySS s n b}
  f (Rtau x) (Rtau y) = mguStar s [(x,y)]
