{-# LANGUAGE ScopedTypeVariables
  , MultiParamTypeClasses
  , FlexibleContexts
  , FlexibleInstances
  , UndecidableInstances
  , TypeSynonymInstances
  , GADTs
  #-}
module RankN where

import Bind
import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import System.IO.Unsafe(unsafePerformIO)
import Monads
import Control.Monad(when,foldM)
import Data.List((\\),nub,union,unionBy,sortBy,groupBy,partition,find)
import Auxillary(Loc(..),plist,plistf,extendM,foldrM,makeNames
                ,DispInfo(..),Display(..),useDisplay,initDI
                ,disp2,disp3,disp4,disp5,dispL,DispElem(..),displays,dv,tryDisplay
                ,maybeM)
import ParserAll  -- This for defining the parser for types
-- To import ParserAll you must define CommentDef.hs and TokenDef.hs
-- These should be in the same directory as this file.
import Data.Char(isLower,isUpper,ord,chr)

import qualified Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.HughesPJ(Doc,text,int,(<>),(<+>),($$),($+$),render)

import SyntaxExt
import Debug.Trace
------------------------------------------------------
-- The Z type is used inside of Display objects as the index

data Z = ZTv TcTv
       | ZInteger Integer

instance Show Z where
  show (ZTv x) = show(TcTv x)
  show (ZInteger n) = "Z"++show n


instance Eq Z where
  (ZTv x) == (ZTv y) = (TcTv x) == (TcTv y)
  (ZInteger x) == (ZInteger y) = x==y
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

showMdisp elems =
  do { d <- readRef dispRef
     ; let (d2,message) = displays d elems
     ; writeRef dispRef d2
     ; return message}

failD :: TyCh m => Int -> [DispElem Z] -> m b
failD n = failK "" n

failK :: TyCh m => String -> Int -> [DispElem Z] -> m b
failK k n elems =  failDd k n elems

failDd k n elems =
   do { d <- readRef dispRef
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
lv n = LvSucc (lv (n-1))

fromLevel LvZero = Just 0
fromLevel (LvSucc x) = fmap (+1) (fromLevel x)
fromLevel (TcLv n) = Nothing

zonkLv :: (Monad m, HasIORef m) => Level -> m Level
zonkLv x = do { a <- pruneLv x; walk a }
 where walk (LvSucc x) = do { y<- zonkLv x; return(LvSucc y)}
       walk x = return x

pruneLv :: (Monad m, HasIORef m) => Level -> m Level
pruneLv (t@(TcLv(LvMut uniq ref))) =
  do { x <- readRef ref
     ; case x of
          Nothing -> return t
          Just y -> do {a <- pruneLv y; writeRef ref (Just a); return a}}
pruneLv x = return x

unifyLevel :: TyCh m => String -> Level -> Level -> m ()
unifyLevel s x y = do { a <- pruneLv x; b <- pruneLv y; walk (a,b)}
  where walk (LvZero,LvZero) = return()
        walk (LvSucc x,LvSucc y) = unifyLevel s x y
        walk (TcLv v,TcLv u) | u==v = return()
        walk (TcLv(v@(LvMut u r)),y) = writeRef r (Just y)
        walk (y,TcLv(v@(LvMut u r))) = writeRef r (Just y)
        walk (x,y) = failD 1 [Ds "\nLevels don't match ",Dd x,Ds " =/= ",Dd y
                             ,Ds ("\n  internal info "++show x++" =/= "++show y)
                             ,Ds ("\n                "++s)]

unifyLev :: String -> Level -> Level -> Maybe[(TcLv,Level)]
unifyLev s x y = walk (x,y)
  where walk (LvZero,LvZero) = Just []
        walk (LvSucc x,LvSucc y) = unifyLev s x y
        walk (TcLv v,TcLv u) | u==v = Just []
        walk (TcLv(v@(LvMut u r)),y) = Just[(v,y)]
        walk (y,TcLv(v@(LvMut u r))) = Just[(v,y)]
        walk (x,y) = Nothing

levelVars x = do { a <- pruneLv x; walk a }
  where walk (TcLv v) = return [v]
        walk (LvSucc x) = levelVars x
        walk LvZero = return[]

 ---  FIX ME
instance TyCh m => TypeLike m Level where
  sub env@(ns,vs,cs,ls) x = subLevel ls x
  zonk x = zonkLv x
  get_tvs x =
     do { zs <- levelVars x
        ; return([],zs)}
  --nf x = zonkLv x

subLevel :: HasIORef a => [(TcLv,Level)] -> Level -> a Level
subLevel env x = do { a <- pruneLv x; walk a }  where
   walk (t@(TcLv v)) = case lookup v env of
                         Nothing  -> return t
                         Just l -> return l
   walk (LvSucc x) = do { a <- subLevel env x; return(LvSucc a) }
   walk x = return x

-- Non computational substitution of levels
substLevel :: [(TcLv,Level)] -> Level -> Level
substLevel env (t@(TcLv v)) =
   case lookup v env of
     Nothing  -> t
     Just l -> l
substLevel env (LvSucc x) = LvSucc(substLevel env x)
substLevel env LvZero = LvZero

varsOfLevel (TcLv v) = ([],[],[v])
varsOfLevel (LvSucc x) = varsOfLevel x
varsOfLevel x = ([],[],[])

newLevel :: TyCh m => m Level
newLevel =
  do { ref <- newRef Nothing
     ; uniq <- nextInteger
     ; return(TcLv(LvMut uniq ref))}

newLevels :: TyCh m => [Name] -> m [(TcLv,Level)]
newLevels names = mapM new names
  where new name = do { n <- newLevel; return(LvVar name,n)}

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
  show (TcLv (LvMut uniq ref)) = "Level"++show uniq
  show (TcLv (LvVar name)) = "_Level"++show name


instance Sht Level where
  shtt LvZero = "0"
  shtt (LvSucc l) = f 1 l
    where f n LvZero = show n
          f n (LvSucc l) = f (n+1) l
          f n l = "("++show n++"+"++show l++")"
  shtt (TcLv (LvMut uniq ref)) = "Mut"++show uniq
  shtt (TcLv (LvVar name)) = "Var"++show name

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

instance NameStore d => Exhibit d TcLv where
  exhibit env v = (env2,s) -- (env2,s++"("++show v++")")
    where (env2,s) = useStoreLevel v id env

instance NameStore d => Exhibit d [(TcLv,Level)] where
  exhibit xs [] = (xs,"[]")
  exhibit xs ys = (zs,"["++ans++"]")
    where (zs,ans) = exhibitL exhibit xs ys ", "

instance NameStore d => Exhibit d Level where
  exhibit env (TcLv v) = (env2,str) -- ++"("++show v++")")
    where (env2,str) = exhibit env v
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

data PolyKind = K [Name] Sigma  -- some Type Constrs have polymorphic kinds!
newtype Kind = MK Tau
data L x = Nil x | Cons (Kind,Quant) (Bind Name (L x))
newtype Sigma = Forall (L ([Pred],Rho))

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


data Flavor = Flexi TRef
            | Rigid Quant Loc (String,IORef(IO String)) -- The IORef(IO String) is only for error reporting,
                                                        -- It has NO SEMANTIC meaning
            | Skol String

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
  solveSomeEqs :: TyCh m => (String,Rho) -> [Pred] -> m ([Pred],Unifier2)
  show_emit :: m Bool
  getTruths :: m[Pred]
  setTruths:: [Pred] -> m a -> m a
  currentLoc:: m Loc
  syntaxInfo:: m [SynExt String]
  normTyFun :: Tau -> m (Maybe Tau)
  fromIO :: IO a -> m a
  getIoMode:: String -> m Bool

handleM n = handleK (const True) n

injectA loc_id preds =
  do { -- whenM (not(null preds)) [Ds "INJECTING ",Ds loc_id,Dd preds];
       injectAccum preds }


type ForAllArgs = [(Name,Kind,Quant)]

class TyCh m => Quantify m t where
  for_all :: [Name] -> ForAllArgs -> t -> m PolyKind

subst env t = sub (env,[],[],[]) t


substPred :: TyCh m => [(Name,Tau)] -> [Pred] -> m[Pred]
substPred [] xs = return xs
substPred env xs = mapM f xs
   where f (Equality x y) = do { a<-(subst env x); b<-(subst env y); return(Equality a b)}
         f (Rel ts) = do { a <- (subst env ts); return(makeRel a)}


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
star1 = MK s1
poly :: Kind -> PolyKind
poly (MK t) = K [] (simpleSigma t)

notEq x y = TyApp (TyApp notEqT x) y

poly1 :: Kind -> (Kind -> Kind) -> PolyKind
poly1 k f = K [](Forall (Cons (k,All) (bind name1 (Nil([],Rtau term)))))
   where MK term = (f (MK(TyVar name1 k)))


unpoly :: PolyKind -> Kind
unpoly (K [] (Forall (Nil([],Rtau tau)))) = MK tau
unpoly x = error ("Can't turn the polykind "++show x++" into a normal kind.")

infixEqName = "(==)"
equalKind = K [](Forall (Cons (star1,All) (bind name1 (Nil ([],ty)))))
   where k = TyVar name1 star1
         ty = Rtau(k `Karr` (k `Karr` propT))

intT =    TyCon Ox (lv 1) "Int" (poly star)
charT =   TyCon Ox (lv 1) "Char" (poly star)
boolT =   TyCon Ox (lv 1) "Bool" (poly star)
orderingT = TyCon Ox (lv 1) "Ordering" (poly star)
listT =   TyCon Ox (lv 1) "[]" (poly star_star)
parserT = TyCon Ox (lv 1) "Parser" (poly star_star)
unitT =   TyCon Ox (lv 1) "()" (poly star)
symbolT = TyCon Ox (lv 1) "Symbol" (poly star)
atomT =   TyCon Ox (lv 1) "Atom" kind4Atom
maybeT =  TyCon Ox (lv 1) "Maybe" (poly star_star)
monadT =  TyCon Ox (lv 1) "Monad" (poly (karr (star_star) star))
pairT =   TyCon pairx (lv 1) "(,)" (poly (karr star (star_star)))
sumT =    TyCon Ox (lv 1) "(+)" (poly (karr star (star_star)))
codeT =   TyCon Ox (lv 1) "Code" (poly star_star)
ioT =     TyCon Ox (lv 1) "IO" (poly star_star)
ptrT =    TyCon Ox (lv 1) "Ptr" (poly star_star)
arrowT =  TyCon Ox (lv 1) "(->)" (poly (karr star (star_star)))
eqT =     TyCon Ox (lv 1) "Equal" kind4Equal
chrSeqT = TyCon Ox (lv 1) "ChrSeq" (poly star)
floatT =  TyCon Ox (lv 1) "Float" (poly star)
stringT = TyApp        listT charT
propT =   TyCon Ox (lv 2) "Prop" (poly star1)
natT =    TyCon Ox (lv 2) "Nat" (poly star1)
notEqT =  TyCon Ox (lv 1) "(!=)" notEqKind

declare (x@(TyCon _ _ name poly)) = (name,x,poly)

-- kind Tag = `name | `age | ... | for all legal symbols
-- data Label :: Tag ~> * where { `name :: Label `name; `age :: Label `age; ... }
tagT    = TyCon Ox (lv 2) "Tag" (poly star1)
labelT  = TyCon Ox (lv 1) "Label" (poly (karr (MK tagT) star))
tagKind = (K [] (simpleSigma tagT))

-- Row :: a ~> b ~> *1
-- kind Row x y = RCons x y (Row x y) | RNil
rowT     = TyCon Ox (lv 2) "Row" (poly (karr star1 star1))

-- RCons :: e ~> f ~> Row e f ~> Row e f
rConsT   = TyCon Ox (lv 2) "RCons" (poly1 star1 f)
           where f k = k `karr` (trow k `karr` trow k)
-- RNil :: Row e f
rNilT    = TyCon Ox (lv 2) "RNil" (poly1 star1 (\ k -> trow k))


kind4Equal :: PolyKind -- Equal :: level b . forall (a:*(1+b)).a ~> a ~> *
kind4Equal = K [] (Forall (Cons (star1,All) (bind name1 (Nil ([],ty)))))
   where k = TyVar name1 star1
         ty = Rtau(k `Karr` (k `Karr` (Star LvZero)))

notEqKind = kind4Equal

kind4Atom :: PolyKind -- Atom :: forall (a:*1).a ~> *
kind4Atom = K [] (Forall (Cons (star1,All) (bind name1 (Nil ([],ty)))))
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
tcode (Rtau x) = Rtau(TyApp codeT x)
tstring = tlist charT
tio x = TyApp ioT x
tptr x = TyApp ptrT x
teq x y = TyApp (TyApp eqT x) y
tlabel x = TyApp labelT x
ttag s = (TyCon Ox (lv 1) s tagKind)
trow (MK x) = MK(TyApp rowT x)
tparser x = TyApp parserT x

tprods [t] = t
tprods (x:xs) = tpair x (tprods xs)

unPair :: Tau -> [Tau]
unPair (TyApp (TyApp (TyCon _ level_ "(,)" k) x) y) = x:(unPair y)
unPair y = [y]

rK :: Rho -> PolyKind
rK rho = K [] (Forall (Nil ([],rho)))

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

-- given m, produce : (String -> m a)
failtype :: TyCh m => Tau -> m Sigma
failtype m =
    do { av <- fresh
       ; let a = TyVar av star
       ; return(Forall
         (Cons (star,All)
               (bind av (Nil ([],Rtau (tstring `tarr` (TyApp m a)))))))}

-- given m, produce : (a -> m a)
returntype :: TyCh m => Tau -> m Sigma
returntype m =
    do { av <- fresh
       ; let a = TyVar av star
       ; return(Forall
         (Cons (star,All)
               (bind av (Nil ([],Rtau (a `tarr` (TyApp m a)))))))}


-- Eq :: level b . forall (a:*(1+b)) (c:a:*(1+b)).Equal c c
sigma4Eq = Forall (Cons (star1,All) (bind kname
                  (Cons (k,All) (bind uname
                  (Cons (k,All) (bind vname (Nil (eqns,Rtau eqty))))))))
   where kname = name1
         uname = name2
         vname = name3
         k = MK(TyVar kname star1)
         u = TyVar uname k
         v = TyVar vname k
         eqns = [Equality u v]
         eqty = TyApp (TyApp eqT u) v


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
  swaps cs (K lvs r) = K (swaps cs lvs) (swaps cs r)

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
-- Zonking, in order to zonk, the monad m must be in the classes (HasNext m,Fresh m)
-- Both the (TyCh m) and IO have these properties. This means we can zonk in the IO monad.

zonkTau :: (HasIORef m, Fresh m) => Tau -> m Tau
zonkTau x = do { y <- prune x; f y}
    where f (TyVar nm k) = do { k2 <- zonkKind k; return(TyVar nm k2)}
          f (TyApp x y) =  binaryLift TyApp (zonkTau x) (zonkTau y)
          f (TyCon sx l s k) =  do { k2 <- zonkPoly k; l2 <- zonkLv l; return(TyCon sx l2 s k2) }
          f (Star n) = do { m <- zonkLv n; return(Star m)}
          f (Karr x y) =  binaryLift Karr (zonkTau x) (zonkTau y)
          f (TyFun nm k x) =  do { y <- mapM zonkTau x; k' <- zonkPoly k; return(TyFun nm k' y) }
          f (TcTv (Tv un flav k)) = do { k2 <- zonkKind k; return(TcTv(Tv un flav k2))}
          f (TySyn nm n fs as t) =
             do { as2 <- mapM zonkTau as; t2 <- zonkTau t
                ; fs2 <- mapM g fs; return(TySyn nm n fs2 as2 t2)}
             where g (nm,k) = do { k2 <- zonkKind k; return(nm,k2)}
          f (TyEx x) = do { w <- zonkL zonkKind zonkPredsTau x; return(TyEx w)}

zonkPredsRho :: (HasIORef a, Fresh a) => ([Pred],Rho) -> a ([Pred],Rho)
zonkPredsRho (preds,rho) = do {ps <- mapM zonkPred preds; r <- zonkRho rho; return(ps,r)}

zonkPredsTau :: (HasIORef a, Fresh a) => ([Pred],Tau) -> a ([Pred],Tau)
zonkPredsTau (preds,tau) = do {ps <- mapM zonkPred preds; t <- zonkTau tau; return(ps,t)}

zonkPred::  (HasIORef m,Fresh m) => Pred -> m Pred
zonkPred (Equality x y) = do { a <- zonkTau x; b <- zonkTau y; return(Equality a b)}
zonkPred (Rel ts) = do {ys <- zonkTau ts; return(makeRel ys)}

zonkRho:: (HasIORef m,Fresh m) => Rho -> m Rho
zonkRho (Rarrow x y) = binaryLift arrow (zonkSigma x) (zonkRho y)
zonkRho (Rpair x y) = binaryLift pair (zonkSigma x) (zonkSigma y)
zonkRho (Rsum x y) = binaryLift rsum (zonkSigma x) (zonkSigma y)
zonkRho (Rtau x) = do { w <- zonkTau x; return(Rtau w)}

zonkKind:: (HasIORef m,Fresh m) => Kind -> m Kind
zonkKind (MK r) = do { r' <- zonkTau r; return(MK r')}

zonkSigma :: (HasIORef m, Fresh m) => Sigma -> m Sigma
zonkSigma (Forall b) = do { w <- zonkL zonkKind zonkPredsRho b; return(Forall w)}

zonkL zk zr (Nil x) = do { w <- zr x; return(Nil w)}
zonkL zk zr (Cons (k,q) b) =
    do { (nm,r) <- unbind b
       ; k' <- zk k
       ; r' <- zonkL zk zr r
       ; return(Cons (k',q) (bind nm r'))}

zonkPoly:: (HasIORef m, Fresh m) => PolyKind -> m PolyKind
zonkPoly (K lvs r) = do { r' <- zonkSigma r; return(K lvs r')}

-------------------------------------------------------------
-- getting type variables

tvs_Tau   :: (HasIORef m,Fresh m) => Tau -> m([TcTv],[TcLv])
tvs_Tau x = do { y <- prune x; f y}
    where f (TcTv (x@(Tv unq _ k))) =
             do { ans <- tvs_Kind k; return(unionP ans ([x],[]))}
          f (TyApp x y) = binaryLift unionP (tvs_Tau x) (tvs_Tau y)
          f (Karr x y) = binaryLift unionP (tvs_Tau x) (tvs_Tau y)
          f (TyFun nm k x) = binaryLift unionP (tvs_Poly k) (tvsList tvs_Tau x)
          f (Star n) = tvs_Level n
          f (TyCon _ level s k) = binaryLift unionP (tvs_Level level) (tvs_Poly k)
          f (TyVar nm k) = tvs_Kind k
          f (TySyn nm n fs as t) = binaryLift unionP (tvsList tvs_Tau as)
                                   (binaryLift unionP (tvsList tvs_Kind (map snd fs)) (tvs_Tau t))
          f (TyEx m) = tvsL tvs_Kind (tvsList tvs_Pred `x` tvs_Tau) m
             where x f g (x,y) = binaryLift unionP (f x) (g y)

tvsList :: (HasIORef m,Fresh m) =>  (x -> m([TcTv],[TcLv])) -> [x] ->  m([TcTv],[TcLv])
tvsList f [] = return ([],[])
tvsList f (x:xs) = binaryLift unionP (f x) (tvsList f xs)

tvsL :: (HasIORef m,Fresh m,Swap x) => (Kind -> m([TcTv],[TcLv])) -> (x -> m([TcTv],[TcLv])) -> L x ->  m([TcTv],[TcLv])
tvsL fk fr (Nil x) = fr x
tvsL fk fr (Cons (k,q) b) = binaryLift unionP (fk k) (tvsL fk fr rest)
  where (_,rest) = unsafeUnBind b

tvs_Rho :: (HasIORef m,Fresh m) => Rho -> m([TcTv],[TcLv])
tvs_Rho (Rarrow x y) = binaryLift unionP (tvs_Sigma x) (tvs_Rho y)
tvs_Rho (Rsum x y) = binaryLift unionP (tvs_Sigma x) (tvs_Sigma y)
tvs_Rho (Rpair x y) = binaryLift unionP (tvs_Sigma x) (tvs_Sigma y)
tvs_Rho (Rtau x) = tvs_Tau x

tvs_Sigma :: (HasIORef m,Fresh m) => Sigma -> m([TcTv],[TcLv])
tvs_Sigma (Forall r) = tvsL tvs_Kind (tvsList tvs_Pred `x` tvs_Rho) r
   where x f g (x,y) = binaryLift unionP (f x) (g y)

tvs_Kind :: (HasIORef m,Fresh m) => Kind -> m([TcTv],[TcLv])
tvs_Kind (MK s) = tvs_Tau s

tvs_Poly :: (HasIORef m,Fresh m) => PolyKind -> m([TcTv],[TcLv])
tvs_Poly (K names sig) = do { (vs,ls) <- tvs_Sigma sig; return(vs,remove ls) }
  where remove [] = []
        remove ((y@(LvVar n)):ys) | n `elem` names = remove ys
        remove (y:ys) = y : (remove ys)

tvs_Level :: (HasIORef m,Fresh m) => Level -> m([TcTv],[TcLv])
tvs_Level (TcLv v) = return([],[v])
tvs_Level (LvSucc x) = tvs_Level x
tvs_Level x = return([],[])

tvs_Pred :: (HasIORef m,Fresh m) => Pred -> m([TcTv],[TcLv])
tvs_Pred (Equality x y) = binaryLift unionP (tvs_Tau x) (tvs_Tau y)
tvs_Pred (Rel ts) = (tvs_Tau ts)

-----------------------------------------------------------------
-- a class that gets type variables and zonks

class (HasIORef m,Fresh m) => Zonk m a where
 zonkG :: a -> m a
 tvs:: a -> m ([TcTv],[TcLv])

instance (HasIORef m,Fresh m) => Zonk m Tau where
 zonkG = zonkTau
 tvs = tvs_Tau

instance (HasIORef m,Fresh m) => Zonk m Rho where
 zonkG = zonkRho
 tvs = tvs_Rho

instance (HasIORef m,Fresh m) => Zonk m Sigma where
 zonkG = zonkSigma
 tvs = tvs_Sigma

instance (HasIORef m,Fresh m) => Zonk m Pred where
 zonkG = zonkPred
 tvs = tvs_Pred

instance (HasIORef m,Fresh m) => Zonk m Kind where
 zonkG = zonkKind
 tvs = tvs_Kind

instance (HasIORef m,Fresh m) => Zonk m PolyKind where
 zonkG = zonkPoly
 tvs = tvs_Poly

instance (HasIORef m,Fresh m) => Zonk m Level where
 zonkG = zonkLv
 tvs = tvs_Level

-- Structured objects are zonkable if the things inside are

instance (Swap r,Zonk m r) => Zonk m (L r) where
  zonkG = zonkL zonkKind zonkG
  tvs x = tvsL tvs_Kind tvs x

instance Zonk m t => Zonk m (Maybe t) where
  zonkG (Just t) = do { x <- zonkG t; return(Just t)}
  zonkG Nothing = return Nothing
  tvs (Just t) = tvs t
  tvs Nothing = return([],[])


instance Zonk m t => Zonk m (Expected t) where
  zonkG (Check t) = do { x <- zonkG t; return(Check t)}
  zonkG (Infer r) = return(Infer r)
  tvs (Check t) = tvs t
  tvs (Infer r) = return([],[])

-- Zonk []  i.e. Lists
instance Zonk m t => Zonk m [t] where
  zonkG ts = mapM zonkG ts
  tvs ts =
    do { vss <- mapM tvs ts
       ; let (ts,ls) = unzip vss
       ; return (nub (concat ts), nub (concat ls)) }

-- Zonk (,)  i.e. Pairs
instance (Zonk m a,Zonk m b) => Zonk m (a,b) where
  zonkG (x,y) = do { a <- zonkG x; b <- zonkG y; return(a,b)}
  tvs (x,y) = binaryLift unionP (tvs x) (tvs y)

-- Zonk (,,)  i.e. Triples
instance (Zonk m a,Zonk m b,Zonk m c) => Zonk m (a,b,c) where
  zonkG (x,y,z) = do { a <- zonkG x; b <- zonkG y; c <- zonkG z; return(a,b,c)}
  tvs (x,y,z) = binaryLift unionP (binaryLift unionP (tvs x) (tvs y)) (tvs z)

instance TyCh m => Zonk m TcTv where
  zonkG x = return x
  tvs x = return ([x],[])

instance TyCh m => Zonk m Char where
  zonkG ts = return ts
  tvs ts = return ([],[])

instance TyCh m => Zonk m Quant where
  zonkG ts = return ts
  tvs ts = return ([],[])

instance TyCh m => Zonk m Name where
 zonkG ts = return ts
 tvs ts = return ([],[])

--------------------------------------------------------------
-- class TypeLike

-- A type is TypeLike if it supports a few primitive operations
-- substitution, zonking, and finding the free type variables.

class (Zonk m t,TyCh m) => TypeLike m t where
  sub :: ([(Name,Tau)],[(TcTv,Tau)],[(String,Tau)],[(TcLv,Level)]) -> t -> m t
  zonk :: t -> m t
  get_tvs :: t -> m ([TcTv], [TcLv])
  zonk = zonkG
  get_tvs = tvs


---------------------------------------------------------------
-- Typelike instances

fromMaybe x Nothing = x
fromMaybe x (Just w) = w

binaryLift f a b = do { x <- a; y <- b; return(f x y)}

unionP (a,b) (x,y) = (union a x, union b y)

rigid (Rigid _ _ _) = True
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
            do { case (lookup x vs, filter ((/=x).fst) vs) of
                  (Just tau, []) -> return tau
                  (Just tau, vs') -> sub (ns,vs',cs,ls) tau
                  (Nothing, _) -> do { k2 <- sub env k; return(TcTv(Tv uniq flav k2))}
               }
          f (TySyn nm n fs as t) =
             do { as2 <- sub env as; t2 <- sub env t
                ; fs2 <- mapM g fs; return(TySyn nm n fs2 as2 t2)}
           where g (nm,k) = do { k2 <- sub env k; return(nm,k2)}
          f (TyEx x) = do { w <- sub env x; return(TyEx w)}

subT env t = sub ([],env,[],[]) t

-- TypeLike Rho
instance TyCh m => TypeLike m Rho where
  sub env (Rarrow x y) = binaryLift arrow (sub env x) (sub env y)
  sub env (Rpair x y)  = binaryLift pair (sub env x) (sub env y)
  sub env (Rsum x y)   = binaryLift rsum (sub env x) (sub env y)
  sub env (Rtau x) = do { w <- sub env x; return(Rtau w)}


-- TypeLike Sigma
instance  TyCh m => TypeLike m Sigma where
  sub env (Forall xs) = do { w <- sub env xs; return(Forall w)}

-- TypeLike PolyKind
instance  TyCh m => TypeLike m PolyKind where
  sub (env@(ws,xs,ys,zs)) (K lvs r) =
        do { lvs2 <- mapM freshName lvs
           ; r' <- sub (ws,xs,ys,lvs2++zs) r; return(K (map getV lvs2) r')}
    where freshName x = do { y <- fresh; return(LvVar x,TcLv(LvVar y))}
          getV (LvVar x,TcLv(LvVar y)) = y

-- TypeLike Kind
instance  TyCh m => TypeLike m Kind where
  sub env (MK r) = do { r' <- sub env r; return(MK r')}

-- TypeLike Equations
instance TyCh m => TypeLike m Pred where
  sub env (Equality x y) = do { a <- sub env x; b <- sub env y; return(Equality a b)}
  sub env (Rel ts) = do {ys <- sub env ts; return(makeRel ys)}

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

instance TypeLike m t => TypeLike m (Maybe t) where
  sub env (Just t) = do { x <- sub env t; return(Just t)}
  sub env Nothing = return Nothing

-- Infer objects are sometime populated with 'doNotPullOnMe'
-- so we never want to pull on them, unless we know
-- they have been overwritten.

instance TypeLike m t => TypeLike m (Expected t) where
  sub env (Check t) = do { x <- sub env t; return(Check t)}
  sub env (Infer r) = return(Infer r)

-- TypeLike []  i.e. Lists
instance TypeLike m t => TypeLike m [t] where
  sub env ts = mapM (sub env) ts

-- TypeLike (,)  i.e. Pairs
instance (TypeLike m a,TypeLike m b) => TypeLike m (a,b) where
  sub env (x,y) = do { a <- sub env x; b <- sub env y; return(a,b)}

-- TypeLike (,,)  i.e. Triples
instance (TypeLike m a,TypeLike m b,TypeLike m c) => TypeLike m (a,b,c) where
  sub env (x,y,z) = do { a <- sub env x; b <- sub env y; c <- sub env z; return(a,b,c)}

instance TyCh m => TypeLike m TcTv where
  sub env x = return x

instance TyCh m => TypeLike m Char where
  sub env ts = return ts

instance TyCh m => TypeLike m Quant where
  sub env ts = return ts

instance TyCh m => TypeLike m Name where
  sub env ts = return ts

-----------------------------------------------
-- Quantify instances

instance TyCh m => Quantify m Tau where
  for_all lvs xs r = return(K lvs (Forall(windup xs ([],Rtau r))))

instance TyCh m => Quantify m Rho where
  for_all lvs xs t = return(K lvs (Forall(windup xs ([],t))))

instance TyCh m => Quantify m Sigma where
  for_all lvs xs (Forall ys)  = return(K lvs (Forall (addToL xs ys)))

instance TyCh m => Quantify m Kind where
  for_all lvs xs (MK r) = for_all lvs xs r

instance TyCh m => Quantify m PolyKind where
  for_all lvs0 xs (K lvs s) = for_all (lvs0++lvs) xs s


instance TyCh m => Quantify m ([Pred],Sigma) where
  for_all lvs xs (eqn,Forall ys) =
    do { (zs,(eqn2,rho)) <- unwind ys
       ; return(K lvs (Forall (windup (xs++zs) (eqn++eqn2,rho))))}

instance TyCh m => Quantify m ([Pred],Rho) where
  for_all lvs xs r = return(K lvs (Forall (windup xs r)))

instance TyCh m => Quantify m ([Pred],Tau) where
  for_all lvs xs (eqs,tau) = return(K lvs (Forall (windup xs (eqs,Rtau tau))))


---------------------------------------------------------------------
-- unify tries to unify to Tau types, This enforces that you can't
-- unify embedded Foralls, or TyVars which only occur inside Foralls

prune :: (Monad a, HasIORef a) => Tau -> a Tau
prune (typ @ (TcTv (Tv uniq (Flexi ref) (MK k)))) =
  do { k2 <- prune k
     ; maybet <- readRef ref
     ; case maybet of
         Nothing -> return (TcTv (Tv uniq (Flexi ref) (MK k2)))
         Just t -> do{t2 <- prune t; writeRef ref (Just t2); return t2}}
prune (typ @ (Star n)) =
  do { n2 <- pruneLv n ; return(Star n2) }
prune (typ @ (TyCon synext l nm k)) =
  do { n2 <- pruneLv l ; return(TyCon synext n2 nm k)}
prune t = return t

pruneV typ v =
  do { theta <- getBindings
     ; case lookup v theta of
         Just new -> if typ==new then return new else prune new
         Nothing -> return typ }


unify :: TyCh m => Tau -> Tau -> m ()
unify x y =
     do { x1 <- prune x; y1 <- prune y
        --; verbose <- getIoMode "verbose"
        --; when verbose (warnM [Ds "\nUnifying ",Dd x1,Ds " =?= ",Dd y1])
        ; f x1 y1
        }
  where f (t1@(TyVar n k)) (t2@(TyVar n1 k1)) | n==n1 = return ()
        f (TyApp x y) (TyApp a b) = do { unify x a; unify y b }
        f (x@(TyCon sx l s _)) (y@(TyCon tx k t _)) =
           do { unifyLevel ("unify TyCon case: "++s++" =?= "++t++show(l,k)) l k
              ; if s==t then return () else matchErr "different constants" x y }
        f (x@(Star n)) (y@(Star m)) = unifyLevel "unify Star case" n m
        f (Karr x y) (Karr a b) = do { unify x a; unify y b }
        f (TySyn nm1 n1 f1 a1 t1) t2 = unify t1 t2
        f t1 (TySyn nm2 n2 f2 a2 t2) = unify t1 t2
        f (x@(TyFun _ _ _)) (y@(TyFun _ _ _)) | x == y = return () -- warnM [Ds "eliminated ", Dd x, Ds " == ", Dd y]
        f (x@(TyFun nm k _)) y = emit x y
        f y (x@(TyFun nm k _)) = emit x y
        f (TcTv x) t = unifyVar x t
        f t (TcTv x) = unifyVar x t
        f (TyEx x) (TyEx y) = unifyEx x y
        f s t = matchErr "\nDifferent types" s t

emit :: TyCh m => Tau -> Tau -> m ()
emit x y =
  do {  a <- zonk x
     ; let f (TcTv(tv@(Tv _ (Flexi _) _))) =
               do { (vs,level_) <- get_tvs x
                  ; if elem tv vs then g else unifyVar tv x}
           f _ = g
           g = do { b <- zonk y
                  ; normM <- normTyFun a
                  ; case normM of
                    Just nonTyfun -> --warnM [ Ds "\nunify instead of emitting (",Dd a,Ds "=?=",Dd b
                                     --      , Ds ")\n     ---> (",Dd nonTyfun,Ds "=?=",Dd b,Ds ")"] >>
                                     unify nonTyfun b
                    Nothing ->
                      do { verbose <- show_emit
                         ; whenM verbose [Ds "\nGenerating predicate\n  ",Dd a, Ds " =?= ",dn b]
                         ; injectA " emitting " [Equality a b]}}
     ; f y}


unifyEx :: TyCh m => L ([Pred],Tau) -> L ([Pred],Tau) -> m ()
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

unifyVar :: TyCh m => TcTv -> Tau -> m ()
unifyVar (x@(Tv u1 r1 k1)) (t@(TcTv (Tv u2 r2 k2))) | u1==u2 = return ()
-- Always bind newer vars to older ones, this way
-- makes the pretty printing work better
unifyVar (x@(Tv u1 (Flexi _) _)) (TcTv(y@(Tv u2 (Flexi _) _)))
  | u1 < u2 = unifyVar y (TcTv x)
unifyVar (x@(Tv u1 (Flexi r1) (MK k))) t =
  do { (vs,level_) <- get_tvs t
     ; t2 <- zonk t
     ; when (elem x vs) (matchErr "Occurs check" (TcTv x) t2)
     --; verbose <- getIoMode "verbose"
     --; when verbose (warnM[Ds "Checking kinds of ",Dd x,Ds " i.e. ",Dd t,Ds ":: ",Dd k])
     ; new_t <- handleM 1 (check t k) (kinderr t k u1)
     ; writeRef r1 (Just t2)
     ; return ()
     }
unifyVar (x@(Tv _ (Rigid _ _ _) _)) (TcTv v@(Tv _ (Flexi _) _)) = unifyVar v (TcTv x)
unifyVar (x@(Tv _ (Skol s) _))      (TcTv v@(Tv u2 (Flexi _) k2))      = unifyVar v (TcTv x)
unifyVar (x@(Tv _ (Rigid _ _ _) _)) (y@(TcTv v@(Tv _ (Rigid _ _ _) _))) =
   do { verbose <- getIoMode "verbose"
      ; bs <- getBindings
      ; whenM verbose [Ds "Emitting ",Dd x,Ds " =?= ", Dd y,Ds "\n",Dl bs ", "]
      ; emit (TcTv x) y }
unifyVar (x@(Tv _ (Rigid _ _ _) _)) (y@(TyCon tx k t _)) = emit (TcTv x) y

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
unifyFun x = failM 0 [Ds "Expected a function type: ",Dd x]


unifyCode :: TyCh a => Expected Rho -> a Rho
unifyCode (Check (Rtau (TyApp (TyCon sx level_ "Code" k) a))) = return (Rtau a)
unifyCode expected =
  do { a <- newRho star; zap a (tcode a) expected }

sigmaTwo :: TyCh m => (Tau -> Tau -> Tau) -> Sigma -> m(Sigma,Sigma)
sigmaTwo mkTwo (Forall xs) =
   do { (tvs,eqs,b) <- unBindWithL [] newFlexi (\ x -> return "FlexVarsShouldNeverBackPatch") xs
      ; (p1,p2) <- case b of
          Rpair x y -> return(x,y)
          Rtau x -> do { a <- newTau star; b <- newTau star
                       ; unify x (mkTwo a b)
                       ; z1 <- zonk a; z2 <- zonk b
                       ; return(simpleSigma z1,simpleSigma z2) }
      ; (mapping,newbinders1,body1) <- subFreshNames [] tvs [] (eqs,p1)
      ; (_,newbinders2,body2) <- subFreshNames [] tvs mapping (eqs,p2)
      ; (K _ sigma1) <- for_all [] newbinders1 body1
      ; (K _ sigma2) <- for_all [] newbinders2 body2
      ; return(sigma1,sigma2) }

sigmaPair :: TyCh m => Sigma -> m (Sigma,Sigma)
sigmaPair t = do { t2 <- zonk t; sigmaP t2}
  where sigmaP (Forall (Nil ([],Rpair x y))) = return (x,y)
        sigmaP x = sigmaTwo tpair x

sigmaSum :: TyCh m => Sigma -> m (Sigma,Sigma)
sigmaSum t = do { t2 <- zonk t; sigmaS t2}
  where sigmaS (Forall (Nil ([],Rsum x y))) = return (x,y)
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
  do { n <- nextInteger
     ; r <- newRef Nothing
     ; return (Tv n (Flexi r) k) }

newRigidTyVar :: TyCh m => Quant -> Loc -> IO String -> Kind -> m TcTv
newRigidTyVar q loc descripComp k =
  do { dummy <- newRef descripComp
     ; n <- nextInteger; return(Tv n (Rigid q loc ("NewRidgidTyVar Call",dummy)) k) }

newSkolTyVar :: TyCh m => String -> Kind -> m TcTv
newSkolTyVar s k =
  do { n <- nextInteger; return(Tv n (Skol s) k) }

-- every var a Skolem var
skolTy :: TyCh m => Sigma -> m ([TcTv],[Pred],Rho)
skolTy sigma = unBindWith (\ x -> return "SkolemVarsShouldNeverBackPatch") newSkolem sigma

-- "new" from "unBindWithL" will be one of these three functions
newFlexi       nam quant k = newTau k
newSkolem      nam quant k = do { v <- newSkolTyVar (show nam) k; return(TcTv v)}
newRigid loc s nam quant k = do { v <- newRigidTyVar quant loc (return s) k; return(TcTv v) }


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
instanTy :: TyCh m => [Name] -> Sigma -> m([Pred],Rho)
instanTy lvs (Forall s) = do { (vs,ps,r) <- instanL lvs s; return(ps,r) }

-- instanL :: (Show b,TypeLike m b, Swap b) =>  [Name] -> L ([Pred],b) -> m ([TcTv],[Pred],b)
instanL lvs s =
  do { levelMap <- newLevels lvs
     ; (vs,eqns,r) <- unBindWithL levelMap newFlexi (\ x -> return "FlexVarsNeverBackPatch3") s
     ; (unifyPred,preds2,r2) <- normalizeEqn eqns r
     ; (u,p,r) <- zonk (unifyPred,preds2,r2)
     ; return(vs,preds2,r2) }



rigidInstance :: TyCh m => (Rho -> IO String) -> String -> PolyKind -> m([TcTv],[Pred],Rho)
rigidInstance inject s (K lvs (Forall zs)) =
  do { loc <- currentLoc
     ; levelMap <- newLevels lvs
     ; unBindWithL levelMap (newRigid loc s) inject zs }

rigidInstanceL inject s lvs zs =
 do { loc <- currentLoc; unBindWithL lvs (newRigid loc s) inject zs }

existsInstance inject s (K lvs (Forall zs)) =
        do { loc <- currentLoc
           ; levelMap <- newLevels lvs
           ; unBindWithL levelMap (new loc) inject zs}
  where new loc name Ex k = newRigid loc s name Ex k
        new loc name All k = newFlexi name All k

--------------------------------------------------------------------

-- each var according to its Quant, either Rigid or Flexi
instanPatConstr :: TyCh a => (Rho -> IO String) -> Quant -> Loc -> [Char] -> PolyKind -> a ([TcTv],[Pred],Rho)
instanPatConstr inject q loc s (K lvs (Forall ty)) =
   do { levelMap <- newLevels lvs
      ; (vs,eqs,r) <- unBindWithL levelMap new inject ty
      ; return(filter p vs,eqs,r) }
   where new nam Ex k = newRigid loc s nam Ex k
         new nam All k = newFlexi nam All k
         p (Tv  uniq (Flexi _) k) = False
         p _ = True

unBindWith :: (TyCh m) => (Rho -> IO String) -> (Name -> Quant -> Kind -> m Tau) -> Sigma -> m ([TcTv],[Pred],Rho)
unBindWith inject new sigma@(Forall b) =
   do { (_,levelvars) <- tvs_Sigma sigma
      ; let freshLevel lv@(LvVar _) = do { new <- newLevel; return (lv, new) }
            freshLevel lv@(LvMut _ _) =
                   do { warnM [ Ds "warning: potentially redundant type variable in\n  "
                              , Dd sigma, Ds "   -- (issue 91)"]
                      ; new <- newLevel;
                      ; return (lv, new) }
      ; levelMap <- mapM freshLevel levelvars
      ; unBindWithL levelMap new inject b }

unBindWithL:: (TypeLike m c, Swap c) =>
              [(TcLv,Level)] -> (Name -> Quant -> Kind -> m Tau) ->
              (c -> IO String) -> L ([Pred],c) -> m ([TcTv],[Pred],c)
unBindWithL lvs new inject b = f b []
 where unTcTv (name,TcTv v) = v
       f (Nil (zs,r)) env =
          do { r' <- subst env r
             ; mapM (patch r') env  -- Rigid variables get backpatched with the type that led to their creation
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
       subst :: TypeLike m c => [(Name,Tau)] -> c -> m c
       subst env t = sub (env,[],[],lvs) t
       patch t (name,x @ (TcTv (Tv unq (Rigid q loc (s,ref)) k))) =
         do { writeRef ref (inject t); return (name,x)}
       patch t (z@(name,x)) = return z



--------------------------------


----------------------------------------------------------------------------
-- The opposite of instantiation (Sigma -> Rho) is quantification
-- (Rho -> Sigma). But in general many other things can be quantified other
-- than Rho. Quantification abstracts over each free TcTv as All Quant
-- variables. Ex Quant vars in Forall's come only from Existential types
-- in data defs. Eg.     data Dyn = exists t . Dyn (Rep t) t
-- so quantify will never produce one.

quantify :: (TypeLike m t,Quantify m t) => [TcLv] -> [TcTv] -> t -> m ([(TcLv,Level)],PolyKind)
quantify lvs tvs ty =
  do { let f v (env,names) = do { nm <- fresh ; return((v,TcLv(LvVar nm)):env,nm:names) }
     ; (levelsub,names) <- foldrM f ([],[]) lvs
     ; (_,newbinders,ty2) <- subFreshNames levelsub tvs [] ty
     ; polyk <- for_all names newbinders ty2
     ; return (levelsub,polyk)
     }

subFreshNames :: (TyCh m,TypeLike m t)
  => [(TcLv,Level)] -> [TcTv] -> [(TcTv,Tau)] -> t -> m( [(TcTv,Tau)],[(Name,Kind,Quant)],t)
subFreshNames lvs [] env ty =
   do { w <- sub ([],env,[],lvs) ty
      ; return(env,[],w) }
subFreshNames lvs (v@(Tv unq (Flexi ref) k):xs) env ty =
   do { name <- fresh
      ; k2 <- sub ([],env,[],lvs) k
      ; (env2,ys,w) <- subFreshNames lvs xs ((v,TyVar name k2):env) ty
      ; return(env2,(name,k2,All):ys,w)
      }
subFreshNames lvs (v:xs) env ty = subFreshNames lvs xs env ty -- ignore non-flexi vars

generalize :: (TypeLike m t,Quantify m t) => t -> m([(TcLv,Level)],PolyKind)
generalize rho =
  do { rho2 <- zonk rho   -- We used to Normalize but this caused problems
     ; (rvars,lvs) <- get_tvs rho2
     ; evars <- envTvs
     ; let generic = filter (not . (`elem` evars)) rvars
     ; (lvs,sig) <- quantify lvs generic rho2
     ; sig2 <- zonk sig
     ; return(lvs,sig2)
     }


-------------------------------------------------------------
-- Typable instances

---------------------------------------------------------------------
-- If a term is Typable as a Rho,
-- one can derive Typability as a Sigma for free!
-- Typability for Tau and Rho depends on the semantics of Term
-- so it is usually defined in the file that defines terms.

polyP (Forall (Cons _ _)) = True
polyP (Forall (Nil _)) = False

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
         ; (preds2,(ls,unifier)) <- solveSomeEqs ("9."++show expr,rho1) preds
         ; rho2 <-  sub ([],unifier,[],ls) rho
         ; let verbose = False
         ; whenM verbose
                  [Ds ("\n(Check term Sigma) The term is: "++ show expr)
                  ,Ds "\nThe type is: ",Dd exp_ty
                  ,Ds "\nskolem is: ",Dd rho
                  ,Ds "\nassump: = ",Dd assump,Ds (show assump)
                  ,Ds "\nSkolem vars are: ",Dl skol_tvs ","
                  ,dv "rho2" rho2]
         ; rho3 <- sub ([],unifier,[],ls) rho2
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
        ; (_,K _ t) <- quantify [] forall_tvs exp_ty
        ; return(t,s) }

------------------------------------------------------
-- How to do Kind inference for all 3 forms of types.
-- Tau :: Tau , Rho :: Tau , and Sigma :: Tau
------------------------------------------------------

getTy (Check s) = return s
getTy (Infer ref) = readRef ref

showKinds:: (TyCh m,TypeLike m a) => (a -> ([TcTv],[(Name,Kind)],[TcLv])) -> a -> m ()
showKinds varsOf t =
 do { t1 <- zonk t
    ; let (free,names,zs) = varsOf t1
    ; whenM (not(null free)) [Ds "\nkinds ",Dlf f free ", "]
    ; whenM (not(null zs)) [Dlf g zs ", "]
    ; whenM (not(null names)) [Dlf h names "\n"]}
 where f disp (v@(Tv un fl k)) = displays disp [Dd v, Ds ":",Dd k]
       g disp l = displays disp [Ds ("level("++show l++") "),Dd l ]
       h disp (nm,k) =  displays disp2 [Ds (" name("++show nm++") "),Ds ss,Ds ":: ",Dd k,Ds ":: ",Dd k,Ds ")"]
          where (disp2,ss) = useStoreName nm star id disp

showKinds2 t =
 do { t1 <- zonkG t
    ; (free,zs) <- tvs t1
    ; return( (if (not(null free)) then [Ds "\nwhere types have kinds:\n   ",Dlf f free "\n   "] else [])++
              (if (not(null zs)) then [Dlf g zs ", "] else []))
    }
 where f disp (v@(Tv un fl k)) = displays disp [Dd v, Ds ":",Dd k]
       g disp l = displays disp [Ds ("level("++show l++") "),Dd l ]

showKinds3 :: Rho -> IO [DispElem Z]
showKinds3 x = showKinds2 x

----------------------------------------------------
-- levels in kind arrow should descend or be equal
-- (x ~> y)  (levelOf x) >= (levelOf y)
-- June 22 2009, We are experimenting with relaxing this rule!!

levelOf x = do { y <- prune x; ans <- get y
               -- ; warnM[Ds "\nLevel of ",Dd y,Ds " = ",Dd ans]
               ; return ans }
  where get (Star n) = do { m <- pruneLv n; return (LvSucc (LvSucc m))}
        get (TyCon _ n _ _) = pruneLv n  -- don't use the kind, since instantiating
                                         -- will invent new level vars.
        get (Karr x y) = get y
        get z = do { k <- kindOfM z
                   ; n <- levelOf k
                   ; predLev n }

dName name = Dlf (\ d name -> useDisplay id d (ZInteger (name2Int name))) [name] ""

predLev :: TyCh m => Level -> m Level
predLev x = do { y <- pruneLv x; help y }
  where help (LvSucc x) = return x
        help LvZero = failM 1 [Ds "Cannot take the predecessor of level 0"]
        help (n@(TcLv(LvMut u r))) =
          do { m <- newLevel; unifyLevel "predLev" n (LvSucc m); pruneLv m }
        help (TcLv (LvVar nm)) =
          failM 1 [Ds "\nLevel '",dName nm,Ds "' is not polymorphic as declared (case 0)."
                  ,Ds "\nWe are trying to force it to be the successor of something."]

freshLevels vs = mapM new vs
  where new s = do { n <- fresh ; return(s,n) }

incLev 0 level = level
incLev n level = incLev (n-1) (LvSucc level)

levelLTE x y LvZero _ = return ()
-- This is an experiment
levelLTE x y _ (LvSucc _) = return ()
-- end experiment

levelLTE x y (LvSucc m) LvZero = notLTE 1 x y
levelLTE x y (LvSucc m) v = do { u <- predLev v; levelLTE x y m u}
levelLTE x y (TcLv v) (TcLv u) | u==v = return ()
levelLTE x y (TcLv(v@(LvMut u r))) m = writeRef r (Just m) >> return ()
levelLTE x y (m@(TcLv (LvVar nm))) (TcLv(v@(LvMut u r))) =  writeRef r (Just m) >> return ()
levelLTE x y (TcLv (LvVar nm)) m = failM 1 [Ds "\nLevel '",dName nm,Ds "' is not polymorphic as declared (case 1).",Ds (shtt m)]

notLTE (n:: Int) (y1,yL) (x1,xL)
   | itsAValue = warnM [Ds "\n\n*** WARNING ***\n",Dd n, Ds " While inferring the kind of: "
                       ,Dd (Karr x1 y1)
                       ,Ds "\nWe find that the level of ",Dd x1,Ds "(", Dd xL,Ds ")"
                       ,Ds " is not >= to the level of ",Dd y1,Ds "(",Dd yL,Dd ")\n"] >> return ()
   | otherwise = return ()
 where itsAValue = case fromLevel yL of
                     Nothing -> True
                     Just m -> m<=1

checkLevelsDescend x1 y1 =
 do { xL <- levelOf x1
    ; yL <- levelOf y1
    ; handleM 2 (levelLTE (y1,yL) (x1,xL) yL xL)
        (\ s -> failM 2 [Ds "We are kinding: ",Dd (Karr x1 y1),Ds ", where "
                      ,Dd x1, Ds " has level ",Dd xL,Ds ", and ",Dd y1,Ds " has level ",Dd yL
                      ,Ds "\nBut, levels don't descend.\n",Ds s])
    }

-- Typable Tau
-- first show that each can be inferred to have a Tau type.
instance TyCh m => Typable m  Tau Tau where
  tc tau expect = do { -- warnM [Ds "\nCheck ",Dd tau, Ds ":?: ",Dd expect];
                       r <- prune tau;  f r expect }
   where
    f t@(TcTv (Tv u r (MK rho))) expect = mustBe ("type","kind") t rho expect
    f t@(TyCon sx level s k) expect = zapPoly t k expect
    f t@(Star n) expect = mustBe ("kind","sort") t (Star (LvSucc n)) expect
    f (Karr x y) expect =
      do { (k :: Tau,x1) <- infer x
         ; y1 <- tc y expect
         ; checkLevelsDescend x1 y1
         ; return(Karr x1 y1) }
    f t@(TyVar n (MK k)) expect = zap2 t k expect
    f t@(TyFun nm (k@(K lvs sig)) xs) expect =
      do { (preds,rho) <- instanTy lvs sig
         ; when (not(null preds)) (failM 0 [Ds "Type functions can't have constrained kinds: ",Dd sig])
         ; ys <- checkTyFun nm rho xs expect
         ; return(TyFun nm k ys)}
    f t@(TyApp ff x) expect =
      do { (fk,a) <- infer ff
         ; fk2 <- zonk fk
         ; (arg_ty,res_ty) <- unifyKindFun ff fk2
         --; warnM [Ds"\ncheckAppCase ",Dd ff,Ds ":: ",Dd fk2,Dd "\n  ",Dd x
         --        ,Ds "\n",Dd arg_ty,Ds " ~> ",Dd res_ty]
         --         ; showKinds varsOfTau (TyApp fk2 (TyApp ff x))
         ; let err mess =
                 do { (inferred::Tau,_) <- infer x
                     ; k <- kindOfM arg_ty
                     ; let but = Dr [ Ds ":: ",Dd k,Ds ") but"]
                     ; failM 2
                       [Ds "\nwhile checking the kind of ("
                       ,Dd t, Ds ")" {- , Ds (shtt t) -}
                       ,Ds "\nwe expected (", Dd x, Ds "::  ",Dd arg_ty,but
                       ,Ds "\nwe inferred (", Dd x, Ds "::  ",Dd inferred,Ds ")\n"
                       ,Ds mess
                       ,case (ff,mess) of
                           (TyCon _ (LvSucc LvZero) "(->)" _,'L':'e':'v':'e':'l':_) ->
                              Ds "\nPerhaps the type arrow (->) should be a kind arrow (~>)"
                           _ -> Ds ""
                       ]}
         ; b <- handleM 2 (check x arg_ty) err
         ; mustBe ("type","kind") t res_ty expect
         ; return (TyApp a b)}
    f t@(TySyn nm n fs as b) expect =
      do { let g (nm,MK k) t = check t k
         ; sequence (zipWith g fs as)
         ; f b expect }
    f (TyEx xs) expect = do { ys <- tc xs expect; return(TyEx ys) }


-- mustBe is a specialized version of zap, with better error reporting
mustBe :: TyCh m => (String,String) -> Tau -> Tau -> Expected Tau -> m Tau
mustBe (term,qual) t comput expect =
   case expect of
    (Check r) -> handleM 1 (unify comput r >> return t) (errZap expect)
    (Infer r) -> handleM 1 (zonk comput >>= writeRef r >> return t) (errZap expect)
  where errZap :: TyCh m => (Expected Tau) -> String -> m a
        errZap (Check r) message =
         do { tz <- zonk t
            ; rz <- zonk r
            ; computz <- zonk comput
            ; failM 1
               [Ds ("\nWe computed the "++term++" ")
               ,Dd tz,Ds (" to have "++qual++" ")
               ,Dd computz,Ds "\nWe expected it to be "
               ,Dd rz,Ds ("\n"++message)
               ]
            }



-- "infer" and "check" walk over a type inferring type information
-- from the structure of the type and information in the type
-- environment. They are placing kind annotations
-- at the leaves (in variables), "kindOfM" walk
-- over an annotated tree and compute the kind of the
-- type. This could be a pure function, except for the
-- possibility of polymorphic TyCon's. Then we need to
-- generate new 'kind variables', so it must be monadic.


kindOfM :: TyCh m => Tau -> m Tau
kindOfM x = do { -- verbose <- getIoMode "verbose";
                 -- when verbose (warnM [Ds "\nKind of  ",Dd x]);
                 f x } where
  f (TcTv (Tv u r (MK k))) = return k
  f (TyCon sx level_ s (K lvs sigma)) =
   do { info <- instanTy lvs sigma
      ; case info of
        (([],Rtau k)) -> return k
        other -> failM 0 [Ds "An illegal kind in a TyCon was found while computing the kind of a type: ",Dd sigma] }
  f (Star n) =  return (Star (LvSucc n))
  f (Karr x y) = kindOfM y
  f (TyVar n (MK k)) = return k
  f (TyFun s (K lvs sigma) ts) =
   do { info <- instanTy lvs sigma
      ; case info of
        ([],Rtau k) -> matchKind k ts
        other -> failM 0 [Ds "An illegal kind in a Type Function was found while computing the kind of a type: ",Dd sigma] }
  f (ty@(TyApp ff x)) =
   do { let (f,ts) = rootTau ty []
      ; k <- kindOfM f
      ; matchKind k ts }
  f (TySyn nm n fs as b) = kindOfM b
  f (TyEx xs) = do { (_,_,t) <- instanL [] xs; kindOfM t}


matchKind :: TyCh m => Tau -> [Tau] -> m Tau
matchKind (Karr a b) (t:ts) =
  do { k <- kindOfM t
     ; unify a k
     ; matchKind b ts }
matchKind k [] = zonk k
matchKind k ts = do { dom <- newUniv
                    ; rng <- newUniv
                    ; let arr = Karr dom rng
                    ; unify arr k
                    ; matchKind arr ts }

checkTyFun :: TyCh m => String -> Rho -> [Tau] -> Expected Tau -> m [Tau]
checkTyFun nm (Rtau k) [] (Infer ref) = do { a <- zonk k; writeRef ref a; return[] }
checkTyFun nm (Rtau k) [] (Check m) = do { morepolyTauTau nm k m; return [] }
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
      --; outputString "IN unifyKindFun"
      ; return (a1,b1) }
unifyKindFun term x = failM 1
         [Ds "\nWhile inferring the kind of the type\n   ",Dd term
         ,Ds "\nWe expected a kind arrow (_ ~> _),\n but inferred: "
         ,Dd x,Ds " instead"]

zap term rho (Check r) = do { morepolyRhoRho (show term) rho r; return term }
zap term rho (Infer r) = do { a <- zonk rho; writeRef r a; return term }

zap2 term tau (Check r) = do { morepolyTauTau (show term) tau r; return term }
zap2 term tau (Infer r) = do { a <- zonk tau; writeRef r a; return term }

zapPoly :: TyCh m => Tau -> PolyKind -> Expected Tau -> m Tau
zapPoly (term@(TyCon sx level s k)) (K lvs sig) expect =
    do { (preds2,rho2) <- instanTy lvs sig  -- ## WHAT DO WE DO WITH THE PREDS?
       ; case rho2 of
            Rtau w -> do { ans <- mustBe ("Constructor","type") term w expect
                         ; let (cname,lev) = getTyConLevel w
                         -- ; warnM [Ds "\nin zapPoly ",Ds (s++"("),Dd level,Ds "):",Ds cname,Ds "(",Dd lev,Ds ")"]
                         ; unifyLevel ("Checking level of constructor: "++s) (LvSucc level) lev
                         ; zonk ans }
            rho -> failM 0 [Ds "An unexpected Rho appeared while kind checking "
                           ,Dd term,Ds " :: ",Dd rho]
       }

getTyConLevel (TyApp (TyApp (TyCon sx _ "(->)" _) x) y) = getTyConLevel y
getTyConLevel (Karr x y) = getTyConLevel y
getTyConLevel x = nameOf x

-- We've drilled down to the range, return name and level of the TyCon
nameOf (TyCon syn level name kind) = (name,level)
nameOf (Star n) = (show(Star n),incLev 2 n)
nameOf (TyApp f x) = nameOf f
nameOf x = ("",LvZero)

zonkT :: TyCh m => Tau -> m Tau
zonkT = zonk

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
    do { (tvs,eqs,b) <- unBindWithL [] newFlexi (\ x -> return "FlexVarsShouldNeverBackPatch4") xs
       ; let err s =  do { ty <- zonk b
                         ; failM 2 [Ds "\nWhile checking well-kindedness of the type\n  "
                                   ,Dd ty,Ds s]}
       ; b2 <- handleM 2 (tc b expect) err
       ; eqs2 <- mapM kindPred eqs
       ; (mapping,newbinders,body) <- subFreshNames [] tvs [] (eqs2,b2)
       ; return(windup newbinders body)
       }

instance TyCh m => Typable m (L([Pred],Tau)) Tau where
  tc xs expect =
    do { (tvs,eqs,b) <- unBindWithL [] newFlexi (\ x -> return "FlexVarsShouldNeverBackPatch5") xs
       ; b2 <- tc b expect
       ; eqs2 <- mapM kindPred eqs
       ; (mapping,newbinders,body) <- subFreshNames [] tvs [] (eqs2,b2)
       ; return(windup newbinders body)
       }

typkind (t@(Tv un f k)) = (t,k)


kindPred :: TyCh m => Pred -> m Pred
kindPred (Equality a b) =
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
  where f d (v@(Tv _ (Rigid All loc (s,ref)) k),t) = displays d  -- USEREF here
           [Ds ("The explict typing: "++s)
           ,Ds ("\nAt "++show loc++" is too polymorphic.")
           ,Ds "\nThe variable ",Dd v
           ,Ds " must be instantiated to ",Dd t]
        f d (Tv _ (Rigid Ex loc (s,ref)) k,t) = displays d -- USEREF here
           [Ds ("An existential type var, arising from the pattern: "++ s)
           ,Ds (" at "++show loc++ " cannot be equal to "),Dd t]


captured sig1 sig2 rho mess =
  failM 0
    [Ds "\nThe type:\n"
    ,Dd sig1,Ds "\nis not more polymorphic than\n"
    ,Dd sig2,Ds ("\n"++"Because the skolemized version of the second type: ")
    ,Dd rho,Ds ("\nhas the following problem: "++mess)]


----------------------------------------------------------------
-- Subsumption 

-- A pair of types can be in subsumption relation if we can
-- ask if one is more polymorphic than another.

morepolyTauTau s x y = -- warnM [Ds "In subsumption Tau Tau ",Dd x,Ds "=?=" ,Dd y] >>
                    unify x y

morepolySigmaSigma :: TyCh m => String -> Sigma -> Sigma -> m ()
morepolySigmaSigma s sigma1 sigma2 =
     do { (skol_tvs,assump,rho) <- skolTy sigma2
        ; (preds,(levelvars,unifier)) <- solveSomeEqs ("morepoly Sigma Sigma",starR) assump
        ; (_,residual::[Pred]) <-
             extractAccum (handleM 1 (assume preds unifier (morepolySigmaRho s sigma1 rho))
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

morepolySigmaExpectedRho s s1 (Check e2) = 
    do { -- warnM [Ds "In subsumption Sigma ExpectedRho Check ",Dd s1,Ds "=?=" ,Dd e2];
         morepolySigmaRho s s1 e2
       }
morepolySigmaExpectedRho s s1 (Infer ref) =
      do { -- warnM [Ds "In subsumption Sigma ExpectedRho Infer ",Dd s1,Ds "=?= Infer"];
           (preds,rho1) <- instanTy [] s1
         ; injectA " morepoly Sigma (Expected Rho) " preds -- ## DO THIS WITH THE PREDS?
         ; writeRef ref rho1
         }
         
instanLevel lvs sig1 = do { env <- mapM f lvs; sub ([],[],[],env) sig1 }
  where f name = do { n <- newLevel; return(LvVar name,n)}

morepolyPolyExpectRho:: TyCh m => String -> PolyKind -> Expected Rho -> m ()  
morepolyPolyExpectRho s (K lvs sig1) rho = 
   do { sigma <- instanLevel lvs sig1
      ; morepolySigmaExpectedRho s sigma rho}

morepolySigmaRho :: TyCh m => String -> Sigma -> Rho -> m ()
morepolySigmaRho s (Forall(Nil([],rho1))) rho2 = morepolyRhoRho s rho1 rho2
morepolySigmaRho s (sigma1@(Forall sig)) rho2 = 
     do {  ts <- getTruths
        ; whenM False [Ds "Entering morepoly Sigma Rho \n Sigma = "
               ,Dd sigma1,Ds "\n Rho = ",Dd rho2
               ,Ds "\n truths = ",Dl ts ", "]
        ; (vs,preds,rho1) <- instanL [] sig
        ; injectA " morepoly Sigma Rho 1 " preds -- ## DO THIS WITH THE PREDS?
        ; ((),oblig2) <- extract(morepolyRhoRho s rho1 rho2)
        ; (local,general) <- localPreds vs oblig2
        -- ; warnM [Ds "\nlocal = ",Dd local,Ds ", general = ", Dd general]
        ; (preds2,(ls,unifier)) <- handleM 1 (solveSomeEqs ("morepoly Sigma Rho",rho2) local)
                                        (no_solution sigma1 rho2 rho1)
        ; gen2 <- sub ([],unifier,[],ls) general
        ; injectA " morepoly Sigma Rho 2 " (gen2++preds2)
        }
 
localPreds vs [] = return ([],[])
localPreds vs (p:ps) =
  do { (loc,gen) <- localPreds vs ps
     ; (free,_) <- get_tvs p
     ; if any (\ x -> elem x vs) free
          then return(p:loc,gen)
          else return(loc,p:gen) }


no_solution sigma rho skoRho s = failM 1
     [Ds "while checking that\n   ", Dd sigma
     ,Ds "\nwas more polymorphic than\n   ",Dd rho
     ,Ds "\nwe skolemized the second to get\n   ", Dd skoRho
     ,Ds ("\nbut, "++s)]



----------------------------------------------------------------

morepolyRhoRho :: TyCh m => String -> Rho -> Rho -> m ()
morepolyRhoRho s  (Rarrow a b) x = do{(m,n) <- unifyFun x; morepolyRhoRho s b n; morepolySigmaSigma s m a }
morepolyRhoRho s  x (Rarrow m n) = do{(a,b) <- unifyFun x; morepolyRhoRho s b n; morepolySigmaSigma s m a }
morepolyRhoRho s  (Rpair m n) (Rpair a b) = do{ morepolySigmaSigma s m a; morepolySigmaSigma s n b }
morepolyRhoRho s  (Rpair m n) x = do{(a,b) <- checkPair x; morepolySigmaSigma s m a; morepolySigmaSigma s n b}
morepolyRhoRho s  x (Rpair a b) = do{(m,n) <- checkPair x; morepolySigmaSigma s m a; morepolySigmaSigma s n b}
morepolyRhoRho s  (Rsum m n) (Rsum a b) = do{ morepolySigmaSigma s m a; morepolySigmaSigma s n b }
morepolyRhoRho s  (Rsum m n) x = do{(a,b) <- checkSum x; morepolySigmaSigma s m a; morepolySigmaSigma s n b}
morepolyRhoRho s  x (Rsum a b) = do{(m,n) <- checkSum x; morepolySigmaSigma s m a; morepolySigmaSigma s n b}
morepolyRhoRho s  (Rtau x) (Rtau y) = morepolyTauTau s x y

morepolyRhoExpectedRho s t1 (Check t2) = morepolyRhoRho s t1 t2
morepolyRhoExpectedRho s t1 (Infer r)  = do { a <- zonk t1; writeRef r a }

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
  | Kinded PT PT
  | TyFun' [PT]
  | TyCon' String (Maybe(Int,String))
  | Star' Int (Maybe String)
  | Forallx Quant [(String,PT,Quant)] [PPred] PT
  | Tlamx String PT
  | AnyTyp -- Gen up a new var with universe polymorphic kind
  | Ext (Extension PT)
  | PolyLevel [String] PT

arityPT:: PT -> Int
arityPT (Rarrow' x y) = 1 + arityPT y
arityPT (Karrow' x y) = 1 + arityPT y
arityPT x = 0

-------------------------------------------

getLevel name (Star' n Nothing) vs = return (lv n)
getLevel name (Star' k (Just s)) vs =
  case lookup s vs of
    Just n -> return(incLev k (TcLv (LvVar n)))
    Nothing -> failM 1 [Ds "\nUnknown level ",Dd s]
getLevel name (Karrow' dom rng) vs = getLevel name rng vs
getLevel name (Rarrow' x y) vs =
  failM 1 [Ds ("\nIn the data declaration for '"++name++"' the range uses a value type arrow (->) use (~>) instead.")]
getLevel name pt vs = failM 1 [Ds ("\nIn the data declaration for '"++name++"' the range:\n   "), Dd pt,Ds "\nis not of the form *n, for some Level n."]

univLevelFromPTkind name (pt@(Forallx q vs preds t)) =
  do { n <- getLevel name t []; return([],n,pt)}
univLevelFromPTkind name (PolyLevel ls (pt@(Forallx q vs preds t))) =
  do { us <- freshLevels ls; n <- getLevel name t us; return(us,n,pt)}
univLevelFromPTkind name pt =
  do { n <- getLevel name pt []; return([],n,pt)}


definesValueConstr (Star' n Nothing) = n==0
definesValueConstr (Star' n (Just s)) = True
definesValueConstr (Karrow' dom rng) = definesValueConstr rng
definesValueConstr (Forallx q vs preds t) = definesValueConstr t
definesValueConstr (PolyLevel ns t) = definesValueConstr t
definesValueConstr x = False

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
  (Kinded pt1 pt2)==(Kinded pt3 pt4) = pt1==pt3 && pt2==pt4
  (TyFun' pts1)==(TyFun' pts2) = pts1==pts2
  (TyCon' s1 _)==(TyCon' s2 _) = s1==s2
  (Star' i1 x)==(Star' i2 y) = i1==i2 && x==y
  (PolyLevel ss x)==(PolyLevel ts y) = ss==ts && x==y
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
getFreeL bnd t free = unionTwo (getFree bnd t) free

unionTwo (x,y) (a,b) = (union x a,union y b)

getFree :: [String] -> PT -> ([String],[String])
getFree bnd (TyVar' s) = if elem s bnd then ([],[]) else ([s],[])
getFree bnd (Rarrow' x y) = unionTwo (getFree bnd x) (getFree bnd y)
getFree bnd (Karrow' x y) = unionTwo (getFree bnd x) (getFree bnd y)
getFree bnd (TyFun' (x:xs)) = foldr (getFreeL bnd) ([],[]) xs
    -- Note that the object in function position (x) is like a TyCon
getFree bnd (TyApp' x y) = (getFree bnd x) `unionTwo` (getFree bnd y)
getFree bnd (Kinded x y) = (getFree bnd x) `unionTwo` (getFree bnd y)
getFree bnd (TyCon' s Nothing) = ([],[])
getFree bnd (TyCon' c (Just(n,""))) = ([],[])  -- corresponds to T_(3), so there are no free variables
getFree bnd (TyCon' c (Just(n,s))) = if elem s bnd then ([],[]) else ([],[s])
getFree bnd (Star' n Nothing) = ([],[])
getFree bnd (Star' n (Just s)) = if elem s bnd then ([],[]) else ([],[s])
getFree bnd (PolyLevel vs t) = getFree (vs++bnd) t
getFree bnd (Tlamx n t) = getFree (n:bnd) t
getFree bnd AnyTyp = ([],[])
getFree bnd (Ext x) = foldr (getFreeL bnd) ([],[]) (extList x)
getFree bnd (Forallx q xs eqs t) = f bnd xs t `unionTwo` g bnd xs eqs
  where f bnd [] t = getFree bnd t
        f bnd ((s,a,q):xs) t = (getFree bnd a) `unionTwo` (f (s:bnd) xs t)

        g bnd ((s,a,q):xs) ys = g (s:bnd) xs ys
        g bnd [] ((Equality' a b):xs) = (getFree bnd a) `unionTwo`
                                        (getFree bnd b) `unionTwo`
                                        g bnd [] xs
        g bnd [] ((Rel' nm ts):xs) = (getFree bnd ts)  `unionTwo` (g bnd [] xs)
        g bnd _ [] = ([],[])

        h bnd t free = unionTwo (getFree bnd t) free

getFreePred bnd (Equality' x y) = getFree bnd x `unionTwo` getFree bnd y
getFreePred bnd (Rel' nm ts) =  getFree bnd ts

getFreePredL bnd xs = foldr g ([],[]) xs
    where g t free = unionTwo (getFreePred bnd t) free


-- Get all the variables appearing in the type, both free and bound

getFL union t free = union (getF union t) free

getF :: (([String],[String])->([String],[String])->([String],[String])) -> PT -> ([String],[String])
getF union (TyVar' s) = ([s],[])
getF union (Rarrow' x y) = union (getF union x) (getF union y)
getF union (Karrow' x y) = union (getF union x) (getF union y)
getF union (TyFun' (x:xs)) = foldr (getFL union) ([],[]) xs
getF union (TyApp' x y) = (getF union x) `union` (getF union y)
getF union (Kinded x y) = (getF union x) `union` (getF union y)
getF union (TyCon' s Nothing) = ([],[])
getF union (TyCon' s (Just(n,lev))) = ([],[lev])
getF union (Star' n Nothing) = ([],[])
getF union (Star' _ (Just n)) = ([],[n])
getF union (Tlamx n t) = getF union t
getF union AnyTyp = ([],[])
getF union (Ext x) = foldr (getFL union) ([],[]) (extList x)
getF union (Forallx q xs eqs t) = f xs t `union` g eqs
  where f [] t = getF union t
        f ((s,a,q):xs) t = (getF union a) `union` (f xs t)
        g [] = ([],[])
        g ((Equality' a b):xs) = (getF union a) `union` (getF union b) `union` g xs
        g ((Rel' nm ts):xs) =(getF union ts) `union` (g xs)


getAll = getF unionTwo
getMult = getF (\ (xs,ys) (ms,ns) -> (xs++ms,ys++ns))


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
  (Kinded x y)  -> do { a <- rcall x; b <- rcall y; return(Kinded a b)}
  (Ext x) -> do { a <- extM rcall x; return(Ext a)}
  (TyCon' s Nothing) -> return(TyCon' s Nothing)
  (TyCon' c (Just(n,s))) ->
       case lookup s sigma of
         Just t -> return(TyCon' c (Just(n,t)))
         Nothing -> return(TyCon' c (Just(n,s)))
  (Star' n Nothing) -> return(Star' n Nothing)
  (Star' n (Just s)) ->
       case lookup s sigma of
         Just t -> return(Star' n (Just t))
         Nothing -> return(Star' n (Just s))
  (PolyLevel ls t) ->
    do { let fresh1 l = do { x1 <- fresh l; return(l,x1)}
       ; newls <- mapM fresh1 ls
       ; t2 <- subPT (newls++sigma) fresh t
       ; return(PolyLevel (map snd newls) t2)}
  AnyTyp -> return AnyTyp
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
  (Kinded x y)  -> Kinded (rcall x) (rcall y)
  (Ext x) -> Ext(fmap rcall x)
  (TyCon' s Nothing) -> (TyCon' s Nothing)
  (TyCon' n (Just(i,s))) ->
      case lookup s sigma of
       Just(Star' _ (Just t)) -> TyCon' n (Just(i,t))
       Nothing -> TyCon' n (Just(i,s))
  (Star' n Nothing) -> Star' n Nothing
  (Star' n (Just s)) ->
      case lookup s sigma of
       Just(Star' _ (Just t)) -> Star' n (Just t)
       Nothing -> Star' n (Just s)
  AnyTyp -> AnyTyp
  (Tlamx n t) -> Tlamx n (ptsub ((n,TyVar' n):sigma) t)
  (Forallx quant xs eqs t) ->
   let sub1 (nm,kind,quant) = (nm,ptsub sigma kind,quant)
       sub2 (Equality' t1 t2) = Equality' (rcall t1) (rcall t2)
       sub2 (Rel' nm ts) = Rel' nm (rcall ts)
    in Forallx quant (map sub1 xs) (map sub2 eqs) (rcall t)
  (PolyLevel ss t) -> PolyLevel ss (rcall t)

ppredsub sub (Equality' x y) = Equality' (ptsub sub x) (ptsub sub y)
ppredsub sub (Rel' x y) = Rel' x (ptsub sub y)

--------------------------------------------------------------------
-- Translating. The translation respects (and enforces) the 3 level
-- distinctions between Sigma, Rho and Tau.

type ToEnv = [(String,Tau,PolyKind)]
type TransEnv = (ToEnv,Loc,[SynExt String],[(String,Name)])

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

toRho :: TyCh m => TransEnv -> PT -> m Rho
toRho env (Rarrow' x y) =
  do { (s,_) <- toSigma env x; r <- toRho env y; return(arrow s r)}
toRho env (TyApp' (TyApp' (TyCon' "(,)" _) x) y) =
  do { (a,_) <- toSigma env x; (b,_) <- toSigma env y; return(pair a b)}
toRho env (TyApp' (TyApp' (TyCon' "(+)" _) x) y) =
  do { (a,_) <- toSigma env x; (b,_) <- toSigma env y; return(rsum a b)}
toRho env t = do { w <- toTau env t; return(Rtau w) }

nonCon x | x==infixEqName = True
nonCon (x:xs) = isLower x
nonCon x = False

-- this quadruple is handy for building the Tpat equivalents
-- of syntactic extensions

extToTpatLift = (lift0,lift1,lift2,lift3)
    where lift0 t = TyCon' t Nothing
          lift1 t x = TyApp' (lift0 t) x
          lift2 t x y = TyApp' (lift1 t x) y
          lift3 t x y z = TyApp' (lift2 t x y) z

-- whenever we translate to a Tau we need a count of how many TyApp nodes
-- we are under, because if we find a TySyn its arity must match the number
-- of nodes we are under. The parameter "n" counts this number. Note how
-- in most recursive calls it is 0.

readName mess ([],loc,exts,levels) s = failM 1 [Ds (mess++" unknown type: "++s)]
readName mess ((x,tau,k):xs,loc,exts,levels) s =
  if s==x
     then --   prune tau
          do { (_,levelvars) <- get_tvs tau
             ; let acc (LvVar x) s = x:s
                   acc _ s = s
                   free = foldr acc [] levelvars
             ; instanLevel free tau }
     else readName mess (xs,loc,exts,levels) s

toTau :: TyCh m => TransEnv -> PT -> m Tau
toTau env x = readTau 0 env x

readTau :: TyCh m => Int -> TransEnv -> PT -> m Tau
readTau n env (TyVar' s) = readName "\nWhile parsing a type var," env s
readTau n env (Rarrow' x y) =
  do { s <- toTau env x; r <- toTau env y; return(tarr s r)}
readTau n env (Karrow' x y) =
  do { s <- toTau env x; r <- toTau env y; return(Karr s r)}
readTau n env (TyCon' (tag@('`':cs)) _) = return (ttag tag)
readTau n (env@(_,loc,_,levels)) (TyCon' s explicit) =
  do { x <- readName "\nWhile parsing a type constructor," env s
     ; case x of
        (TySyn nm m fs as x) | m>n -> failM 0 [Ds ("Type synonym: "++nm++" applied to few args")]
        (TySyn nm m fs as x) | m<n -> failM 0 [Ds ("Type synonym: "++nm++" applied to many args")]
        x -> case (explicit,x) of
              (Just(i,""),TyCon ext _ nm k) -> return(TyCon ext (incLev i LvZero) nm k)
              (Just(i,v),TyCon ext _ nm k) ->
                 case lookup v levels of
                    Just lev -> return(TyCon ext (incLev i (TcLv (LvVar lev))) nm k)
                    Nothing -> failM 1 [Ds ("\n\n"++ show loc),Ds ("\nUnknown level: "++v)]
              other -> return x
     }
readTau n env (Star' m Nothing) = return(Star (lv m))
readTau n (env@(_,loc,_,levels)) (Star' k (Just m)) =
  case lookup m levels of
   Just lev -> return(Star (incLev k (TcLv (LvVar lev))))
   Nothing -> failM 1 [Ds ("\n\n"++ show loc),Ds ("\nUnknown level: "++m)]
readTau n env (TyApp' x y) =
  let (funtyp,argtyps) = root x [y]
  in do { f <- readTau (length argtyps) env funtyp
        ; xs <- mapM (toTau env) argtyps
        ; case f of
           (TySyn nm m fs as b) ->
               do { let subst = zipWith (\ (nm,k) t -> (nm,t)) fs xs
                  ; body <- sub (subst,[],[],[]) b
                  ; return(TySyn nm n fs xs body)}
           _ -> return(applyT (f:xs)) }
readTau n env (Kinded t k) =
  do { kind <- toTau env k
     ; tau <- toTau env t
     ; check tau kind
     ; zonk tau}
readTau n env (ty@(TyFun' (x:xs))) =
  do { s <- toTau env x
     -- ; d1 <- warnM [Ds "\n Entering ",Dd ty,Ds "\n",Dl env ","]
     ; ys <- mapM (toTau env) xs
     ; case s of
        TyCon sx level_ nm k | nonCon nm -> return(TyFun nm k ys)
        TyCon sx level_ nm k -> failM 0 [Ds ("The name of a type function must begin with a lower case letter: "++nm)]
        _ -> failM 0 [Ds "\n",Dd ty
                     ,Ds " doesn't have a type function name in the function position of type function application: "
                     ,Dd s,Ds ("   "++sht s)]}
readTau n env AnyTyp = newUniv
readTau n env (t@(Forallx Ex xs eqs body)) =
   do { (_,fargs,env2) <- argsToEnv xs env
      ; r <- toTau env2 body
      ; eqs2 <- toEqs env2 eqs
      ; return(TyEx(windup fargs (eqs2,r))) }
readTau n env (Forallx All [] [] body) = readTau n env body
readTau n (env@(zs,loc,_,_)) (t@(Forallx All xs [] body)) =
  do { (env2@(ws,_,_,_)) <- generalizePTargs xs env
     ; warnM [Ds ("\n\n"++ show loc),Ds "\n****** Just a warning ******\n\n",Ds "Sigma type in Tau context: ", Dd t]
     ; warnM [Ds "is being generalized. This might not be what you expect."]
     ; ans <- readTau n env2 body
     ; zonk  ans }     
readTau n (env@(_,loc,_,_)) (t@(Forallx q xs eqs body)) =     
  failM 1 [Ds ("\n\n"++ show loc),Ds "\nSigma type in Tau context: ", Dd t]
readTau n (env@(_,loc,_,_)) (t@(PolyLevel _ _)) =
  failM 1 [Ds ("\n\n"++ show loc),Ds "\nLevel polymorphic type in Tau context: ", Dd t]
readTau n env (t@(Tlamx s x)) = failM 1 [Ds "No lambda types in rankN: ",Dd t]
readTau n env (Ext x) =
  do { exts <- syntaxInfo
     ; loc <- currentLoc
     ; new <- buildExt (show loc) extToTpatLift x exts
     ; readTau n env new
     }


root (TyApp' f y) ys = root f (y:ys)
root f ys = (f,ys)

argsToEnv :: TyCh m => [(String,PT,Quant)] -> TransEnv -> m ([(String,Name)],ForAllArgs,TransEnv)
argsToEnv [] env = return([],[],env)
argsToEnv ((s,k,quant):xs) (env@(toenv,loc,exts,levels)) =
 do { w <- toTau env k
    ; let k2 = MK w
    ; nm <- fresh
    ; (ns,zs,env2) <- argsToEnv xs ((s,TyVar nm k2,poly k2):toenv,loc,exts,levels)
    ; return ((s,nm):ns,(nm,k2,quant):zs,env2)
    }
    
generalizePTargs :: TyCh m => [(String,PT,Quant)] -> TransEnv -> m TransEnv
generalizePTargs [] env = return env
generalizePTargs ((s,k,quant):xs) (env@(toenv,locs,exts,levels)) =
 do { kind <- toTau env k
    ; let k2 = MK kind
    ; tau <- newTau k2
    ; generalizePTargs xs ((s,tau,poly k2):toenv,locs,exts,levels) }    

------------------------------------------------------
tunit' = TyCon' "()" Nothing

prodT' = TyCon' "(,)" Nothing
prod' x y = TyApp' (TyApp' prodT' x) y

tprods' [] = tunit'
tprods' [t] = t
tprods' (x:xs) = prod' x (tprods' xs)

sumT' = TyCon' "(+)" Nothing
sum' x y = TyApp' (TyApp' sumT' x) y
tsums' [t] = t
tsums' (x:xs) = sum' x (tsums' xs)

listT' = TyCon' "[]" Nothing
list' x = TyApp' listT' x

arr' x y = Rarrow' x y

applyT' [t] = t
applyT' [TyCon' "(->)" _,x,y] = Rarrow' x y
applyT' [x,y] = TyApp' x y
applyT' (x : y : z) = applyT' ((TyApp' x y):z)

------------------------------------------------------------------
-- parsing simple types, ones that never need parenthesizing

parse_tag inject =
     try (do { whiteSpace
             ; char '`'
             ; v <- ident
             ; notFollowedBy (char '`')
             ; whiteSpace
             ; return(inject v)})
  where ident = do{ c <- identStart tokenDef
                  ; cs <- many (identLetter tokenDef)
                  ; return (c:cs)
                  } <?> "identifier"

extToPT (Pairx (Right xs) "") = tprods' xs
extToPT (Listx (Right [x]) Nothing "") = list' x
extToPT x = Ext x

conName = lexeme (try construct)
  where construct = do{ c <- upper
                      ; cs <- many (identLetter tokenDef)
                      ; return(c:cs)}
                    <?> "Constructor name"

explicitCon = lexeme (try construct)
  where construct = do{ cs <- conName
                      ; let (last,name) = trailing cs
                      ; clevel <- conlevel last
                      ; return (TyCon' (fix clevel name cs) clevel) }
                    <?> "Constructor with explicit level"
        fix Nothing short long = long
        fix (Just _) short long = short

trailing x =
  case reverse x of
    ('_' : more) -> ('_',reverse more)
    other -> ('#',x)

conlevel:: Char -> Parser(Maybe(Int,String))
conlevel '#' = return Nothing
conlevel '_' = (underbar <|> (return Nothing)) <?> "Explicit constructor level"
  where underbar = (parens plusexp) <|> (return Nothing)
num = do { ds <- many1 digit; return((read ds)::Int)}
plusexp = try prefixPlus <|> try postfixPlus <|> try justnum <|> try justvar <|> (return Nothing)
justnum = do { i <- num; return(Just(i,""))}
justvar = do { n <- identifier; return(Just(0::Int,n))}
prefixPlus = do { i <- num; char '+'; n <- identifier; return(Just(i,n)) }
postfixPlus = do { n <- identifier;  char '+'; i <- num; return(Just(i,n)) }

backQuoted a = do { whiteSpace
                  ; char '`'
                  ; a' <- a
                  ; char '`'
                  ; whiteSpace
                  ; return a' }

applied item op = do { item1 <- item
                     ; more <- try quoted <|> (fmap Right $ many item)
                     ; return $ case more of
                                Left [v, item2] -> [v, item1, item2]
                                Right more -> item1:more }
  where quoted = do { v <- backQuoted op
                    ; item2 <- item
                    ; return (Left [v, item2]) } <?> "quoted infix type operator"

parseStar :: Parser PT
parseStar = lexeme(do{char '*'; (n,k) <- star; return(Star' n k)})
  where star = (do { s <- ident; return(0,Just s)}) <|>                -- This comes first, otherwise we'd always get just "*"
               (parens (fmap fix (prefixPlus <|> postfixPlus))) <|>    -- then this. Order matters
               (do { ds <- many digit; return (val ds,Nothing)})
        fix:: Maybe(Int,String) -> (Int,Maybe String)
        fix Nothing = (0,Nothing)
        fix (Just(i,"")) = (i,Nothing)
        fix (Just(i,s)) = (i,Just s)


tyCon0 x = TyCon' x Nothing

tyIdentifier = fmap TyVar' identifier

simpletyp :: Parser PT
simpletyp =
       fmap extToPT (extP typN)                          -- [x,y ; zs]i  (a,b,c)i
   <|> lexeme explicitCon                                -- T
   <|> (parse_tag (\ s -> TyCon' ("`"++s) (Just(1,"")))) -- `abc
   <|> tyIdentifier                                      -- x
   <|> parseStar                                         -- * *1 *2
   <|> fmap extToPT natP                                 -- #2  4t (2+x)i
   <|> try (fmap tyCon0 (symbol "()" <|> symbol "[]"))   -- () and []
   <|> try (do { x <- parens(symbol "->" <|>             -- (->) (+) (,) and (==)
                             symbol "+"  <|>
                             symbol ","  <|>
                             symbol "==")
               ; return(TyCon' ("("++x++")") Nothing)})

   <|> try(do { ts <- parens(sepBy1 typN (symbol "+"))  -- (t+t+t)
              ; return (tsums' ts)})
   <|> try(parens(do { t <- typN; symbol "::"; k <- typN; return(Kinded t k)}))
   <|> do { t <- squares typN; return (list' t)}       -- [t]
   <|> do { xs <- braces (applied simpletyp tyIdentifier)
          ; return(TyFun' xs) }                        -- {f x y} or {x `f` y}


val :: String -> Int
val [] = 0
val xs = read xs

data ArrowSort
  = Single   -- ->
  | Wavy     -- ~>
  | Fat      -- =>
  | InfixEq  -- ==

arrTyp :: Parser PT
arrTyp =
   do { ts <- applied simpletyp explicitCon -- "f x y -> z" or "x `f` y" parses as "(f x y) -> z"
      ; let d = (applyT' ts)                -- since (f x y) binds tighter than (->)
      ; range <- possible
           ((do {symbol "->"; ans <- typN; return(Single,ans)})  <|>
            (do {symbol "~>"; ans <- typN; return(Wavy,ans)})    <|>
            (do {symbol "=="; ans <- typN; return(InfixEq,ans)})
           )
      ; case range of
           Nothing -> return d
           Just(Single,r) -> return(Rarrow' d r)
           Just(Wavy,r) -> return(Karrow' d r)
           Just(InfixEq,r) -> return(TyFun' [TyCon' infixEqName Nothing,d,r])
      }

allPrefix:: Parser (Quant,[(String,PT,Quant)])
allPrefix =
    do { q2 <- (reserved "forall" >> return All) <|>
               (reserved "exists" >> return Ex)
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
  (do { x <- identifier; return(x,AnyTyp,q)}) <|>
  (parens (do { x <- identifier
              ; reservedOp "::"
              ; k <- typN
              ; return(x,k,q) }))


typN :: Parser PT
typN = allTyp <|> arrTyp <|> parens typN

------------------------------------------------

qual = reservedOp "=" >> return "="

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

isTyConAp (TyApp' (TyApp' (TyCon' "(,)" _) x) y) = Nothing
isTyConAp (TyApp' (TyCon' t _) x) = Just t
isTyConAp (TyApp' (TyVar' t) x) = Just t
isTyConAp (TyApp' f x) = isTyConAp f
isTyConAp x = Nothing

props :: Parser [PPred]
props = (try (do { x <- proposition; symbol "=>"; return[x]})) <|>
          (try (do { xs <- parens(sepBy proposition comma)
                   ; symbol "=>"; return xs}))                     <|>
          (return [])

-- A typing has many forms, some are listed below
-- f :: a -> b                              simple
-- f :: P a => a -> b                       qualified
-- f :: a=b => a -> b                       equality qualified
-- f :: (a=b,P a) => a -> b                 multiply qualified
-- f :: forall a b . (a=b,P a) => a -> b    explicit forall
-- Nat :: level b . *b                             -- Level polymorphic tycon
-- T:: level b . x ~> *(b+1)                       -- Level polymorphic
-- f :: level b . forall (a::*b) . a -> a -> *0    -- Level polymorphic args

typingHelp =
  do { reservedOp "::"
     ; levels <- level
     ; prefix <- possible allPrefix
     ; preds <- props
     ; body <- typN
     ; return(levels,prefix,preds,body)
     }

level :: Parser [String]
level = try (do { symbol "level"; ls <- many1 identifier; symbol "."; return ls})
        <|> (return [])

typing =
  do { (declaredLevels,prefix,preds,body) <- typingHelp
     ; let (predfree,levels1) = getFreePredL [] preds
           (bodyfree,levels2) = getFree [] body
     ; okLevels declaredLevels (nub (levels1 ++ levels2))
     ; case prefix of
        Nothing -> let free = nub(predfree++bodyfree)
                       f x = (x,AnyTyp,All)
                   in return(declaredLevels,Forallx All (map f free) preds body)
        Just(q2,ns) -> return (declaredLevels,Forallx q2 ns preds body)
     }

okLevels declared found | declared /= nub declared =
  let bad = declared \\ nub declared
      n = head bad
  in unexpected ("\nDuplicate level variable: "++n++", in 'level' declaration.")
okLevels declared found =
  let extra = found \\ declared
  in if null extra
        then return ()
        else let n = head extra
             in unexpected ("\nThe level variable: "++n++", is not declared."++
                            "\nUse 'level "++n++" .  type -> *"++n++"', for example.")

--------------------------------------------------------

pt s = case parse2 typN s of { Right(x,more) -> return x; Left s -> fail s }
parsePT s = pt s

intThenTyp n = do { m <- try (possible natural); t <- typN; return (pick m,t)}
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

peqt s = case parse2 arrTyp s of { Right(x,more) -> x; Left s -> error s }

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


instance (NameStore d,Exhibit d a, Exhibit d b) => Exhibit d (a,b) where
  exhibit d (x,y) = (d2,"("++sx++","++sy++")")
    where (d1,sx) = exhibit d x
          (d2,sy) = exhibit d1 y

instance NameStore d => Exhibit d PPred where
  exhibit d (Equality' x y) = (d,"Equal "++show x++" "++show y)
  exhibit d (Rel' nm ts) = (d,show ts)

instance NameStore d => Exhibit d PT where
  exhibit d x = (d,show x)


instance Show PT where
  show (TyVar' s) = s
  show (Rarrow' x y) = showp x ++ " -> "++show y
  show (Karrow' x y) = showp x ++ " ~> "++show y
  show (TyApp' (TyCon' "[]" _) x) = "[" ++ show x ++ "]"
  show (TyApp'(TyApp'(TyCon' "(,)" _) x) y)= "("++show x++","++show y++")"
  show (TyApp'(TyApp'(TyCon' "(+)" _) x) y)= "("++show x++"+"++show y++")"
  show (TyApp'(TyApp'(TyCon' "(!=)" _) x) y)= show x++" != "++show y
  show (TyApp' x (y@(TyApp' _ _))) = show x ++ " " ++ showp y
  show (TyApp' x y) = show x ++ " " ++ showp y
  show (Kinded x y) = "("++show x ++ "::" ++ showp y ++")"
  show (TyCon' s Nothing) = s
  show (TyCon' s (Just(0,v))) = s++"_"++v
  show (TyCon' s (Just(i,""))) = s++"_("++show i++")"
  show (TyCon' s (Just(i,v))) = s++"_("++show i++"+"++v++")"
  show (TyFun' xs) = plistf f "{" xs " " "}"
    where f (x@(TyApp' _ _)) = "("++show x++")"
          f (x@(Rarrow' _ _)) = "("++show x++")"
          f (x@(Karrow' _ _)) = "("++show x++")"
          f x = show x
  show (Star' n Nothing) = "*"++show n
  show (Star' 0 (Just n)) = "*"++n
  show (Star' k (Just n)) = "*("++show k++"+"++n++")"
  show (Tlamx n t) = "("++n++" . "++show t++")"
  show AnyTyp = "?"
  show (Ext x) = show x
  show (PolyLevel ls t) = "level"++plistf id " " ls " " ". "++show t
  show (Forallx q2 xs eqs t) = showQ xs q2 ++ f xs++ g eqs ++ show t ++ close xs ")"
    where f [(s,AnyTyp,q)] =  shq q ++ s ++ " . "
          f ((s,AnyTyp,q):xs) = shq q++ s ++ " "++f xs
          f [(s,k,q)] = "("++  shq q++ s ++"::" ++ show k ++") . "
          f ((s,k,q):xs) = "("++  shq q ++ s++"::" ++ show k ++") "++f xs
          f [] = ""
          g [] = ""
          g xs = plistf show "(" xs "," ") => "
          shq All = ""
          shq Ex  = "_"
          showQ [] _ = ""
          showQ (x:xs) q = showquant q
          close [] paren = ""
          close (x:xs) paren = paren

instance Sht PT where
  shtt (TyVar' s) = "(TyVar' "++s++ ")"
  shtt (Rarrow' x y) = shtt x ++ " -> "++shtt y
  shtt (Karrow' x y) = shtt x ++ " ~> "++shtt y
  shtt (TyApp' x y) = "(TyApp' "++shtt x ++ " " ++ shtt y++")"
  shtt (Kinded x y) = "(Kinded "++shtt x ++ " " ++ shtt y++")"
  shtt (TyCon' s Nothing) =  "(TyCon' "++s++ ")"
  shtt (TyCon' s (Just(0,v))) = "(TyCon' "++s++"_"++v++")"
  shtt (TyCon' s (Just(i,""))) = "(TyCon' "++s++"_("++show i++"))"
  shtt (TyCon' s (Just(i,v))) = "(TyCon' "++s++"_("++show i++"+"++v++"))"

  shtt (TyFun' xs) = plistf f "{" xs " " "}"
    where f (x@(TyApp' _ _)) = "("++shtt x++")"
          f (x@(Rarrow' _ _)) = "("++shtt x++")"
          f (x@(Karrow' _ _)) = "("++shtt x++")"
          f x = shtt x
  shtt (Star' n Nothing) = "*"++show n
  shtt (Star' 0 (Just n)) = "*"++n
  shtt (Star' k (Just n)) = "*("++show k++"+"++n++")"
  shtt (PolyLevel ls t) = "(level"++plistf id " " ls " " "."++shtt t++")"
  shtt (Tlamx n t) = "("++n++" . "++shtt t++")"
  shtt AnyTyp = "AnyTyp"
  shtt (Forallx q2 xs eqs t) =  "(Forallx ... )"

showquant All = "(forall "
showquant Ex = "(exists "

showp x@(Rarrow' _ _) = "("++show x ++ ")"
showp x@(Karrow' _ _) = "("++show x ++ ")"
showp (t@(TyApp' (TyCon' "[]" _) x)) = show t
showp (t@(TyApp'(TyApp'(TyCon' "(,)" _) x) y)) = show t
showp (t@(TyApp'(TyApp'(TyCon' "(+)" _) x) y)) = show t
showp x@(TyApp' _ _) = "("++show x ++ ")"
showp x@(Forallx q _ _ _) = "("++show x ++ ")"
showp x = show x




--------------------------------------------------------------
-- show instances

isRow :: Tau -> Bool
isRow (TyApp (TyApp (TyCon sx _ c _) x) y) | recordCons c sx || leftRecordCons c sx = True
isRow (TyCon sx _ c _) | recordNil c sx || leftRecordNil c sx = True
isRow _ = False

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
-- Side-effect free substitution. Usually you must zonk
-- before calling these functions.

type Unifier2 = ([(TcLv,Level)],[(TcTv,Tau)])

sub2Kind :: Unifier2 -> Kind -> Kind
sub2Kind ([],[]) x = x
sub2Kind env (MK x) = MK(sub2Tau env x)

sub2Poly :: Unifier2 -> PolyKind -> PolyKind
sub2Poly ([],[]) x = x
sub2Poly env (K lvs s) = K lvs(sub2Sigma env s)

sub2Sigma :: Unifier2 -> Sigma -> Sigma
sub2Sigma ([],[]) x = x
sub2Sigma env (Forall xs) = Forall(sub2L env xs)

sub2L :: Unifier2 -> L ([Pred],Rho) -> L ([Pred],Rho)
sub2L ([],[]) xs = xs
sub2L env (Nil(eqn,rho)) = Nil(sub2Pred env eqn,sub2Rho env rho)
sub2L env (Cons (k,q) x) = Cons (sub2Kind env k,q) (bind nm xs)
  where (nm,more) = unsafeUnBind x
        xs = sub2L env more

sub2LTau :: Unifier2 -> L ([Pred],Tau) -> L ([Pred],Tau)
sub2LTau ([],[]) xs = xs
sub2LTau env (Nil(eqn,rho)) = Nil(sub2Pred env eqn,sub2Tau env rho)
sub2LTau env (Cons (k,q) x) = Cons (sub2Kind env k,q) (bind nm xs)
  where (nm,more) = unsafeUnBind x
        xs = sub2LTau env more

sub2Pred :: Unifier2 -> [Pred] -> [Pred]
sub2Pred ([],[]) xs = xs
sub2Pred env xs = map f xs
   where f (Equality x y) = Equality (sub2Tau env x) (sub2Tau env y)
         f (Rel ts) = makeRel (sub2Tau env ts)


sub2Pairs :: Unifier2 -> [(Tau,Tau)] -> [(Tau,Tau)]
sub2Pairs ([],[]) xs = xs
sub2Pairs env xs = map f xs where f (x,y) = (sub2Tau env x,sub2Tau env y)

sub2TcTv:: Unifier2 -> TcTv -> TcTv
sub2TcTv env (var@(Tv unq flav k)) =
   case sub2Tau env (TcTv var) of
     TcTv u -> u
     _ -> Tv unq flav (sub2Kind env k)

sub2Rho :: Unifier2 -> Rho -> Rho
sub2Rho ([],[]) x = x
sub2Rho env (Rarrow s r) = Rarrow (sub2Sigma env s) (sub2Rho env r)
sub2Rho env (Rpair s r) = Rpair (sub2Sigma env s) (sub2Sigma env r)
sub2Rho env (Rsum s r) = Rsum(sub2Sigma env s) (sub2Sigma env r)
sub2Rho env (Rtau t) = Rtau(sub2Tau env t)

sub2Tau :: Unifier2 -> Tau -> Tau
sub2Tau ([],[]) x = x
sub2Tau (env@(lvs,vs)) (TcTv (x@(Tv unq flav k))) =
   case lookup x vs of
      Nothing -> TcTv (Tv unq flav (sub2Kind env k))
      Just z -> z
sub2Tau env (TyApp x y) =  TyApp (sub2Tau env x) (sub2Tau env y)
sub2Tau (env@(ls,_)) (TyCon sx l s k) = TyCon sx (substLevel ls l) s k2
  where k2 = sub2Poly env k
sub2Tau (ls,vs) (Star n) = Star (substLevel ls n)
sub2Tau env (Karr x y) =  Karr (sub2Tau env x) (sub2Tau env y)
sub2Tau env (TyFun f k x) = TyFun f (sub2Poly env k) (map (sub2Tau env) x)
sub2Tau env (TyVar s k) = TyVar s (sub2Kind env k)
sub2Tau env (TySyn nm n fs as x) = TySyn nm n (map f fs) (map (sub2Tau env) as) (sub2Tau env x)
  where f (nm,k) = (nm,sub2Kind env k)
sub2Tau env (TyEx e) = TyEx(sub2LTau env e)

subRho env x = sub2Rho ([],env) x
subTau env x = sub2Tau ([],env) x
subSigma env x = sub2Sigma ([],env) x
subPairs env x = sub2Pairs ([],env) x
subPred env x = sub2Pred ([],env) x
subTcTv env x = sub2TcTv ([],env) x
---------------------------------------------------
-- Get type variables from a term, should be zonked first

union2 (x,y) (a,b) = (union x a,unionBy f y b)
  where f (n1,k1) (n2,k2) = n1==n2

union3 (x,y,z) (a,b,c) = (union x a,unionBy f y b,union z c)
  where f (n1,k1) (n2,k2) = n1==n2

varsOfTcTv (x@(Tv unq flav (MK k))) = union3 (varsOfTau k) ([x],[],[])

varsOfTau :: Tau -> ([TcTv],[(Name,Kind)],[TcLv])
varsOfTau (TcTv x) = varsOfTcTv x
varsOfTau (TyApp x y) = union3 (varsOfTau x) (varsOfTau y)
varsOfTau (Karr x y) = union3 (varsOfTau x) (varsOfTau y)
varsOfTau (TyFun f k xs) = union3 (varsOfPoly k) (foldr g ([],[],[]) xs)  where g t vs = union3 (varsOfTau t) vs
varsOfTau (Star n) = varsOfLevel n
varsOfTau (TyCon sx l s k) = varsOfPoly k `union3` varsOfLevel l
varsOfTau (TyVar s k) = union3 ([],[(s,k)],[]) (varsOfKind k)
varsOfTau (TySyn nm n fs xs x) =
      union3 (varsOfTau x)
             (union3 (foldr h ([],[],[]) fs) (foldr g ([],[],[]) xs))
   where g t vs = union3 (varsOfTau t) vs
         h (nm,k) vs = union3 (varsOfKind k) vs
varsOfTau (TyEx x) = (varsOfLTau x)

varsOfList :: (a -> ([TcTv],[(Name,Kind)],[TcLv])) -> [a] -> ([TcTv],[(Name,Kind)],[TcLv])
varsOfList f [] = ([],[],[])
varsOfList f (x:xs) = union3 (f x) (varsOfList f xs)

varsOfTauTauL = varsOfList (varsOfPair varsOfTau varsOfTau)

varsOfPoly(K lvs x) = case varsOfSigma x of
                       (vs,nms,ls) -> (vs,nms,ls \\ map LvVar lvs)
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

varsOfExpectRho (Check r) = varsOfRho r
varsOfExpectRho (Infer ref) = ([],[],[])

varsOfPair f g (x,y) = (xs++ys, as++bs, ms++ns)
  where (xs,as,ms) = f x
        (ys,bs,ns) = g y

fst3 (x,y,z) = x
tvsTau x = fst3 (varsOfTau x)


---------------------------------------------------------------
-- Computing most general unifiers. Done in a side-effect free way.
-- Note that Flexi vars might be bound in the unifier returned.
-- A computational pass can force these to be unified later if
-- necessary. See the function "mutVarSolve" and "mguM"

a = TcTv(Tv 5 (Skol "a") star)
b = TcTv(Tv 6 (Skol "b") star)
c = TcTv(Tv 7 (Skol "c") star)

ps = [Equality b a, Equality c a]

failIfInConsistent pat current extension xs =
  do { ans <- mguB xs
     ; case ans of
        Right ("No Match",x,y) ->
          failK "bad refinement" 2
            [Ds "in the scope of ",Ds pat,Ds "\nThe current refinement\n   "
            ,Dl current ",",Ds "\nis inconsistent with the refinement extension\n   "
            ,Dl extension "," ,Ds "\nbecause ",Dd x, Ds " =/= ",Dd y]
        _ -> return (map (uncurry Equality) xs) }

subLev env (t@(TcLv v)) =
  case lookup v env of
         Nothing  -> t
         Just l -> l
subLev env (LvSucc x) = LvSucc(subLev env x)
subLev env x = x

compose2 (Left xs) (Left ys) = Left(composeTwo xs ys)
compose2 _ (Right x) = Right x
compose2 (Right y) _ = Right y

composeTwo (l1,s1) (l2,s2) =
    ([(l,subLev l1 t) | (l,t) <- l2] ++ l1,[(u,subTau s1 t) | (u,t) <- s2] ++ s1)

compose (Left (s1)) (Left (s2)) = Left ([(u,subTau s1 t) | (u,t) <- s2] ++ s1)
compose _ (Right x) = Right x
compose (Right y) _ = Right y


o s1 s2 = [(u,subTau s1 t) | (u,t) <- s2] ++ s1

-- (compose new old) and (new `o` old) assume that the new refinement
-- has a disjoint set of variables. This is the case in "mgu" because
-- a variable is processed and removed from the rest of the term, so
-- it never occurs again. But in some contexts this is not the case.
-- in this situation one might have (compose [(x,5),(y,3)] [(x,f),(z,y)])
-- Now we expect [(x,f),(z,3),(y,3)] and the equality [f == 5]

extendref :: [(TcTv,Tau)] -> [(TcTv,Tau)] -> ([(TcTv,Tau)],[(Tau,Tau)])
extendref new old = ([(u,subTau fresh t) | (u,t) <- old] ++ fresh,existing)
  where (fresh,existing) = foldr acc ([],[]) new
        acc (u,exp) (fresh,existing) =
          case find (\ (v,term) -> u==v) old of
            Just (v,term) -> (fresh,(exp,term):existing)
            Nothing -> ((u,exp):fresh,existing)

-------------------------------------------------------
-- mguB is monadic, but it never binds variables
-- it may generate fresh variables but only to get the kind
-- of a term.

mostGenUnify :: TyCh m => [(Tau,Tau)] -> m (Maybe ([(TcLv,Level)],[(TcTv,Tau)]))
mostGenUnify xs =
  do { ans <- mguB xs
     ; case ans of
        Left ans -> return (return ans)
        Right (s,x,y) -> return(fail s) }

eitherM :: Monad m => m (Either a b) -> (a -> m c) -> (b -> m c) -> m c
eitherM comp leftf rightf =
  do { x <- comp
     ; case x of
         Left y -> leftf y
         Right y -> rightf y}


mguLevelB::  TyCh m => Level -> Level -> [(Tau,Tau)] -> m(Either Unifier2 (String,Tau,Tau))
mguLevelB LvZero LvZero xs = mguB xs
mguLevelB (LvSucc x) (LvSucc y) xs = mguLevelB x y xs
mguLevelB (TcLv v) x xs =
   do { zs <- mguB xs; return(compose2 (Left([(v,x)],[])) zs)}
mguLevelB x (TcLv v) xs =
   do { zs <- mguB xs; return(compose2 (Left([(v,x)],[])) zs)}
mguLevelB a b xs = return(Right("levels don't match",Star a, Star b))

mguB :: TyCh m => [(Tau,Tau)] -> m(Either Unifier2 (String,Tau,Tau))
mguB [] = return(Left([],[]))
mguB ((TcTv (Tv n _ _),TcTv (Tv m _ _)):xs) | n==m = mguB xs

mguB ((TcTv (x@(Tv n (Flexi _) _)),tau):xs) = mguBVar x tau xs
mguB ((tau,TcTv (x@(Tv n (Flexi _) _))):xs) = mguBVar x tau xs

mguB ((TyApp x y,TyApp a b):xs) = mguB ((x,a):(y,b):xs)
mguB ((TyCon sx level1 s1 _,TyCon tx level2 s2 _):xs) | s1==s2 =
  eitherM (mguLevelB level1 level2 [])
    (\u1 -> do { u2 <- mguB (sub2Pairs u1 xs) ; return(compose2 u2 (Left u1))})
    (\x -> return(Right x))
mguB ((Star n,Star m):xs) =
  eitherM (mguLevelB n m [])
    (\ u1 -> do { u2 <- mguB (sub2Pairs u1 xs) ; return(compose2 u2 (Left u1))})
    (\ x -> return(Right x))
mguB ((Karr x y,Karr a b):xs) = mguB ((x,a):(y,b):xs)
mguB ((x@(TyFun f _ ys),y@(TyFun g _ zs)):xs) =
  if f==g then mguB (zip ys zs ++ xs) else return(Right("TyFun doesn't match",x,y))
mguB ((x@(TyVar s k),y):xs) = return(Right("No TyVar in MGUB", x, y))
mguB ((y,x@(TyVar s k)):xs) = return(Right("No TyVar in MGUB", x, y))
mguB ((TySyn nm n fs as x,y):xs) = mguB ((x,y):xs)
mguB ((y,TySyn nm n fs as x):xs) = mguB ((y,x):xs)

mguB ((TcTv (x@(Tv n (Rigid _ _ _) _)),tau):xs) = return(Right("Rigid",TcTv x,tau))
mguB ((tau,TcTv (x@(Tv n (Rigid _ _ _) _))):xs) = return(Right("Rigid",TcTv x,tau))

mguB ((x,y):xs) = return(Right("No Match", x, y))

-- mguBVar is only called from mguB
--
mguBVar :: TyCh m => TcTv -> Tau -> [(Tau,Tau)] -> m(Either Unifier2 ([Char],Tau,Tau))
mguBVar (x@(Tv n _ _)) (tau@(TyFun _ _ _)) xs | elem x (tvsTau tau) =
  do { norm <- normTyFun tau
     ; case norm of
       Just (TcTv (Tv m _ _)) | n==m -> mguB xs
       Just tau' -> if elem x (tvsTau tau')
                    then return(Right("occurs check (after normalization)", TcTv x, tau'))
                    else mguBVar x tau' xs
       _ -> return(Right("occurs check (not normalizable)", TcTv x, tau))
     }
mguBVar (x@(Tv _ _ (MK k))) tau xs | elem x (tvsTau tau) = return(Right("occurs check", TcTv x, tau))
mguBVar (x@(Tv _ _ (MK k))) tau xs =
  do { let new1 = ([],[(x,tau)])
     ; k2 <- kindOfM tau
     ; new2 <- mguB (sub2Pairs new1 ((k,k2):xs))
     ; return(compose2 new2 (Left new1))
     }



----------------------------------------------------------------------
-- While Matching, One assumes only variables on the left can match
-- And, that such variables never appear on the right.

{-
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
-}


match2 :: Monad m => Unifier2 -> [(Tau,Tau)] -> m Unifier2
match2 env [] = return env
match2 env ((TcTv (Tv n _ _),TcTv (Tv m _ _)):xs) | n==m = match2 env xs
match2 env ((TcTv (x@(Tv n (Flexi _) _)),tau):xs) = match2Var env x tau xs
match2 env ((TyApp x y,TyApp a b):xs) = match2 env ((x,a):(y,b):xs)
match2 env ((TyCon sx level1 s1 _,TyCon tx level2 s2 _):xs) | s1==s2 =
  matchLevel env level1 level2 xs
match2 env ((Star n,Star m):xs) = matchLevel env n m xs
match2 env ((Karr x y,Karr a b):xs) = match2 env ((x,a):(y,b):xs)
match2 env ((x@(TyFun f _ ys),y@(TyFun g _ zs)):xs) =
  if f==g then match2 env (zip ys zs ++ xs) else fail "TyFun doesn't match"
match2 env ((x@(TyVar s k),y):xs) = fail "No TyVar in match"
match2 env ((y,x@(TyVar s k)):xs) = fail "No TyVar in match"
match2 env ((TySyn nm n fs as x,y):xs) = match2 env ((x,y):xs)
match2 env ((y,TySyn nm n fs as x):xs) = match2 env ((y,x):xs)
match2 env ((x,y):xs) = fail "No Match"

match2Var :: Monad m => ([(TcLv, Level)], [(TcTv, Tau)]) -> TcTv -> Tau -> [(Tau, Tau)] -> m Unifier2
match2Var (env@(ls,vs)) x tau xs =
    case find (\ (v,t) -> v==x) vs of
      Just (v,t) -> if t==tau then match2 env xs else fail "Duplicate"
      Nothing -> match2 (ls,(x,tau):vs) xs

matchLevel :: Monad m => Unifier2 -> Level -> Level -> [(Tau, Tau)] -> m Unifier2
matchLevel env LvZero LvZero xs = match2 env xs
matchLevel env (LvSucc x) (LvSucc y) xs = matchLevel env x y xs
matchLevel (env@(ls,vs)) (TcLv x) l xs =
   case find (\ (v,t) -> v==x) ls of
     Just (v,t) -> if t==l then match2 env xs else fail "Duplicate"
     Nothing -> match2 ((x,l):ls,vs) xs
matchLevel env _ _ _ = fail "No Match"


--------------------------------------------------------------------

x2 = [(v 843,Star LvZero)
     ,(v 764,Karr (v 843) (v 845))
     ]

v n = TcTv(Tv n (Rigid All Z (show n,undefined)) star)
u n = (Tv n (Rigid All Z (show n,undefined)) star)


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
 where v n = TcTv(Tv n (Rigid All Z (show n,undefined)) star)
       u n = v n

-- go = mguB test2

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
  shtt (ps,s) = shttL shtt ps ++ " => "++shtt s

instance Sht [(Tau,Tau)] where
  shtt xs = plistf f "\n[   " xs ",\n   " "]"
    where f (x,y) = "("++sht x++","++sht y++")"

instance Sht [Pred] where
  shtt xs = plistf shtt "[" xs "," "]"

{-
instance Sht x => Sht [x] where
  shtt xs = plistf shtt "[" xs "," "]"
-}

shttL f xs = plistf f "[" xs "," "]"

instance Sht Kind where
  shtt (MK s) = shtt s
instance Sht Name => Sht PolyKind where
  shtt (K lvs z) = (if null lvs then "(" else "(level "++shttL shtt lvs ++".")++shtt z++")"
instance Sht Name where
  shtt x = show x

shtP (x,y) = "("++shtt x++"," ++ shtt y++")"

sht (TyVar n k) = "(TyVar "++show n++"::"++shtt k++")"
sht (TyApp x y) = "(TyApp "++sht x++" "++sht y++")"
sht (TyCon sx l x k) = "(Con "++x++"@"++show l {- ++" %"++show sx -}  ++")"
                     --  ++":"++shtt k++")"
sht (Star n) = "(Star "++show n++")"
sht (Karr x y) = "(Karr "++sht x++" "++sht y++")"
sht (TcTv (Tv n (Flexi _) k))  = "(Flex " ++ show n ++":"++shtt k++")"
sht (TcTv (Tv n (Skol _) k))  = "(Skol " ++ show n ++shtt k++")"
sht (TcTv (Tv n (Rigid _ _ _) k))  =
    "(Rigid " ++ show n ++":"++shtt k++")"
sht (TyFun nm k xs) = "{TyFun ("++nm ++ "::"++shtt k++")"++plistf sht " " xs " " "}"
sht (TySyn nm n fs as t) = "{Syn "++nm++(plistf sht " " as " " " = ")++sht t++"}"
sht (TyEx l)= shtL l

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

shtL xs = let (ys,(eqs,a)) = unsafeUnwind xs
              f [] = ""
              f [(nm,MK k,_)] = show nm
              f ((nm,MK k,_):xs) = show nm++f xs
          in "(exists "++(f ys)++"."++shtt a++")"

-- =============================================================
-- New style Display
-- =============================================================

class NameStore d where
   useStore:: Integer -> (String -> String) -> d -> (d,String)
   useStoreChoose:: [String] -> Integer -> (String -> String) -> d -> (d,String)
   -- You only need to define one of these
   useStoreChoose choices uniq f d = useStore uniq f d
   useStore uniq f d = useStoreChoose infiniteNames uniq f d

infiniteNames = makeNames "abcdefghijklmnopqrstuvwxyz"


-----------------------------------------------------
-- lifting this to types that can produce documents

class DocReady t where
   dDoc:: NameStore d => d -> t -> (d,Doc)

data Docs where
   Dx :: DocReady x => x -> Docs
   Dsp :: Docs
   Doc :: Doc -> Docs
   Dds :: String -> Docs

docs :: [Docs] -> DispElem Z
docs xs = Df f xs
 where f d xs = (d2,render (PP.cat docs))
           where (d2,docs) = threadx d xs
       threadx :: (NameStore t) => t -> [Docs] -> (t, [Doc])
       threadx d [] = (d,[])
       threadx d (Dx x :xs) = (d2,y : ys)
          where (d1,y) = dDoc d x
                (d2,ys) = threadx d1 xs
       threadx d (Dsp :xs) = (d,text " " : ys)
          where  (d2,ys) = threadx d xs
       threadx d (Dds s :xs) = (d,text s : ys)
          where  (d2,ys) = threadx d xs
       threadx d (Doc doc : xs) = (d2,doc : ys)
          where  (d2,ys) = threadx d xs

---------------------------------------------------------
-- NameStore instances

useStoreLevel (LvMut uniq ref) f env = useStore uniq ((++"L") . f) env
useStoreLevel (LvVar name) f env = useStore (name2Int name) f env
useStoreName name kind newname d = useStore (name2Int name) newname d
useStoreTcTv (Tv uniq flavor kind) f d = useStore uniq f d

instance NameStore (DispInfo Z) where
  useStore uniq f env = useDisplay f env (ZInteger uniq)

useStoreNameE nm k f xs = useStoreChoose (choices k) nm f xs

instance NameStore [(Name,String)] where
  useStoreChoose choices nm f xs = case lookup uniq xs of
                       Just s -> (xs,s)
                       Nothing -> ((uniq,new):xs,new)
    where uniq = (integer2Name nm)
          new = f(first xs choices)
          first old (x:xs) = if find x old then first old xs else x
          find x [] = False
          find x ((_,y):old) = if x==y then True else find x old

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

instance NameStore () where
  useStore uniq f xs = (xs,short uniq)

short n = charName (fromInteger(n `mod` 26)) : digitize (n `div` 26)
charName n | n < 26 = chr(ord 'a' + n)
charName n = chr(ord '0' + (n - 26))
digitize n =
  case n `div` 36 of
    0 -> [charName (fromInteger(n `mod` 36))]
    m -> (digitize m) ++ [charName(fromInteger(n `mod` 36))]

-----------------------------------------------------------------

class NameStore d => Exhibit d t where
  exhibit :: d -> t -> (d,String)

instance NameStore d => Exhibit d Integer where
  exhibit d n = (d,show n)

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

-- exhibit a TcTv
exhibitTv :: NameStore a => a -> TcTv -> (a,String)
exhibitTv d1 (x@(Tv _ flav (MK k))) = (d3,str)
                                      -- (d3,"("++str++":"++kstr++")")
  where (d2,str) = useStoreTcTv x (tVarPrefix flav) d1
        (d3,kstr) = exhibit d2 k

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



---------------------------------------------------------------
-- Now some instances for exhibiting different type like things
-- All these are parameterized by "d" being a NameStore

instance NameStore d => Exhibit d Int where
  exhibit d n = (d,show n)

instance Exhibit (DispInfo Z) Bool where
  exhibit d n = (d,show n)

-- Kind
instance NameStore d => Exhibit d Kind where
  exhibit d1 (MK k) = exhibit d1 k

instance NameStore d => Exhibit d Name where
  exhibit d1 nm = useStoreName nm star id d1

-----------------------------------------------
-- Exhibiting Syntactic Extensions in Tau types

postscript "" = ""
postscript a = a

exSynNat d (TyApp (TyCon synext _ c k) x)| natSucc c synext = f d 1 x
  where f d n (TyCon ext _ c k)          | natZero c ext    = (d,show n++ postscript (synKey ext))
        f d n (TyApp (TyCon ext _ c k) x)| natSucc c ext    = f d (n+1) x
        f d n v = let (d2,ans) = exhibit d v
                  in (d2,"("++show n++"+"++ans++ ")" ++ postscript (synKey synext))
exSynNat d v = (d,"Ill-formed Natural number extension: "++shtt v)

exSynTick d (TyApp (TyCon synext _ c k) x)| tickSucc c synext = f d 1 x
  where f d n (TyApp (TyCon ext _ c k) x) | tickSucc c ext    = f d (n+1) x
        f d n v = let (d2,ans) = exhibit d v
                  in (d2,"("++ ans ++"`"++ show n ++ ")" ++ postscript (synKey synext))
exSynTick d v = (d,"Ill-formed Tick extension: "++shtt v)

exhibitNmK xs (nm,k) = useStoreName nm k ("'"++) xs          -- One or the other
                      -- (zs,"("++ans++":: "++k2++")")
    where (ys,ans) = useStoreName nm k ("'"++) xs
          (zs,k2) = exhibit ys k

-- polyLevel _ = True -- For debugging purposes to see levels of constructors
polyLevel LvZero = False
polyLevel (LvSucc x) = polyLevel x
polyLevel x = True


pp:: Exhibit (DispInfo Z) t => t -> IO ()
pp x = putStrLn (snd (exhibit disp0 x))

-- =========================================================================
-- turning type-like things into documents:  Doc


instance DocReady Tau where
  dDoc = dTau
instance DocReady Rho where
  dDoc = dRho
instance DocReady Sigma where
  dDoc = dSigma
instance DocReady Kind where
  dDoc = dKind
instance DocReady PolyKind where
  dDoc = dPoly
instance DocReady Pred where
  dDoc = dPred

simple (d,s) = (d,text s)
docToString (d,doc) = (d,render doc)

thread:: (d -> x -> (d,Doc)) -> Doc -> d -> [x] -> (d,[Doc])
thread f sep d [] = (d,[])
thread f sep d [x] = (d2,[ans])
  where (d2,ans) = f d x
thread f sep d (x:xs) = (d2,y<>sep:ys)
  where (d1,y) = f d x
        (d2,ys) = thread f sep d1 xs

arrowTau :: NameStore t => t -> Tau -> (t, [Doc])
arrowTau d (TyApp (TyApp (TyCon sx _ "(->)" _) x) y) = (d3, (contra x doc <> text " -> "):docs)
  where (d2,doc) = dTau d x
        (d3,docs) = arrowTau d2 y
        contra (TyApp (TyApp (TyCon _ _ "(->)" _) _) _) d = PP.parens d
        contra _ d = d
arrowTau d x = (d2,[doc])
  where (d2,doc) = dTau d x

arrowRho :: NameStore t => t -> Rho -> (t, [Doc])
arrowRho d (Rarrow s r) = (d3,lhs : docs)
  where (d2,doc) = dSigma d s
        (d3,docs) = arrowRho d2 r
        lhs = PP.parens doc <> text " -> "
arrowRho d (Rtau x) = arrowTau d x
arrowRho d x = (d2,[doc])
  where (d2,doc) = dRho d x

dTau:: (NameStore d) => d -> Tau -> (d,Doc)
dTau xs (t@(TyCon ext _ c _))           | natZero c ext = (xs,text ("0" ++ postscript (synKey ext)))
dTau xs (t@(TyApp (TyCon ext _ c _) x)) | natSucc c ext = simple (exSynNat xs t)
dTau xs (t@(TyApp (TyCon ext _ c _) x)) | tickSucc c ext = simple (exSynTick xs t)
dTau xs (t@(TyCon ext _ s _))           | listNil s ext || leftListNil s ext = (xs, text("[]"++postscript (synKey ext)))
dTau xs (t@(TyApp (TyApp (TyCon ext _ c _) _) _)) | listCons c ext = exSynListD xs t
dTau xs (t@(TyApp (TyApp (TyCon ext _ c _) _) _)) | leftListCons c ext = exSynLeftListD xs t
dTau xs (t@(TyCon ext _ s _))                     | recordNil s ext || leftRecordNil s ext = (xs, text ("{}"++postscript (synKey ext)))
dTau xs (t@(TyCon ext _ s _))                     | unitUnit s ext = (xs, text ("()"++postscript (synKey ext)))
dTau xs (t@(TyApp (TyCon ext _ s _) _))           | itemItem s ext = exSynItemD xs t
dTau xs (t@(TyApp (TyApp (TyApp (TyCon ext _ c _) _) _) _))
                                                  | recordCons c ext = exSynRecordD xs t
dTau xs (t@(TyApp (TyApp (TyApp (TyCon ext _ c _) _) _) _))
                                                  | leftRecordCons c ext = exSynLeftRecordD xs t
dTau xs (t@(TyApp (TyApp (TyCon ext _ c _) _) _)) | pairProd c ext || leftPairProd c ext = exSynPairD xs t

{-
dTau xs (TyCon _ l nm (K vs k)) |  nm `elem` []  -- to debug, use something like: ["L","Bush"]
         = (ys,text nm <> parens (text l' <> PP.comma <> PP.hcat vs' <> text "." <> k'))
     where (ys,l') = exhibit xs l
           (ws,vs') = thread dSigma PP.comma ys (map LvVar vs)
           (zs,k') = dTau ws k
-}

dTau xs (t@(TyCon _ l s k))| polyLevel l = (ys,text (s++"_")<> text y)
      where (ys,y) = exhibit xs l
dTau xs (t@(TyCon _ l s k)) = (xs,text s)
dTau e (TyApp (TyCon sx _ "[]" _) x) = (ys, PP.brackets ans)
    where (ys,ans) = dTau e x
dTau e (TyApp (TyApp (TyCon sx _ "(,)" _) x) y) = (zs, PP.parens (a <> PP.comma <> b))
    where (ys,a) = dTau e x
          (zs,b) = dTau ys y
dTau e (t@(TyApp (TyApp (TyCon sx _ "(->)" _) x) y)) = (d3,PP.cat list)
    where (d3,list) = arrowTau e t
dTau e (TyApp (TyApp (TyCon sx _ "(+)" _) x) y) = (zs, PP.parens (a <> text "+" <> b))
    where (ys,a) = dPar e x
          (zs,b) = dPar ys y
dTau xs (TyApp x y) = (zs,a <> text " " <> b)
    where (ys,a) = dTau xs x
          (zs,b) = dPar ys y
dTau xs (Star LvZero) = (xs,text "*0")
dTau xs (Star n) = (ys, text ("*" ++ str))
     where (ys,str) = exhibit xs n
dTau xs (TyVar nm k) = (d,text ans)
   where (d,ans) = exhibitNmK xs (nm,k)
dTau xs (Karr x y) = (zs,a <> text " ~> " <> b)
    where (ys,a) = dArrow xs x
          (zs,b) = dTau ys y
dTau info (TcTv v) = (d,text s)
  where (d,s) = exhibitTv info v
dTau info (TyFun f k xs) = (d2,text ("{"++f++" ")<> PP.cat body <> text "}")
    where (d2,body) = thread dPar (text " ") info xs
dTau info (TySyn nm n fs as t) = (d2,text (nm++" ")<> PP.cat xs)
    where (d2,xs) = thread dPar (text " ") info as
dTau xs (TyEx x) = (d,s)
   where (d,s) = dLdata Ex xs x

dRho:: (NameStore d) => d -> Rho -> (d,Doc)
dRho xs (Rtau x) = dTau xs x
dRho xs (t@(Rarrow x y)) = (d3,PP.cat list)
    where (d3,list) = arrowRho xs t
dRho xs (Rpair x y) = (zs,PP.parens (a <> PP.comma <> b))
  where (ys,a) = dSigma xs x
        (zs,b) = dSigma ys y
dRho xs (Rsum x y) = (zs,PP.parens (a <> text "+" <> b))
  where (ys,a) = dSigma xs x
        (zs,b) = dSigma ys y

dSigma d1 (Forall args) = dLdata All d1 args

dKind:: NameStore a => a -> Kind -> (a,Doc)
dKind d (MK t) = dTau d t

dPoly:: (NameStore d) => d -> PolyKind -> (d,Doc)
dPoly d1 (K lvs (Forall args)) = (d3,levels <> s1)
   where (d2,s1) = dLdata All d1 args
         (d3,s2) = if null lvs
                      then (d2,PP.empty)
                      else let (d4,list) = thread dBind (text " ") d2 lvs
                           in (d4,PP.sep list)
         dBind d x = (d2,text s) where (d2,s) = exhibit d x
         levels = if null lvs
                     then PP.empty
                     else (text "level " <> s2 <> text " . ")

ppPoly x = render (snd(dPoly (initDI :: DispInfo Z) x))

dPred:: (NameStore d) => d -> Pred -> (d,Doc)
dPred xs (Rel ts) = dTau xs ts
dPred xs (Equality x y) = (zs,text "Equal " <> PP.sep[a,b])
    where (ys,a) = dPar xs x
          (zs,b) = dPar ys y

dKinding :: NameStore a => a -> Tau -> (a,Doc)
dKinding d1 (Star LvZero) = (d1,text "*0")
dKinding d1 (t@(Star n)) = (d2,text("*"++nstr))
   where (d2,nstr) = exhibit d1 n
dKinding d1 (TyVar nm (MK k)) = (d3,text nmStr <> text "::" <> kStr)
   where (d2,nmStr) = useStoreName nm (MK k) f d1 where f s = "'"++s
         (d3,kStr) = dKinding d2 k
dKinding d1 (TcTv (v@(Tv _ _ (MK k)))) = (d3,text nmStr <> text "::" <> kStr)
   where (d2,nmStr) = exhibitTv d1 v
         (d3,kStr) = dKinding d2 k
dKinding d1 (TyCon sx (LvSucc LvZero) s k) = (d1,text s)
dKinding d1 (TyCon sx l s k) = (d2,text (s++"::") <> sorting)
  where (d2,sorting) = dPoly d1 k
dKinding d1 (x@(Karr _ _)) = (d2,s) where (d2,s)= dDoc d1 x
dKinding d1 (x@(TyApp _ _)) = (d2,s) where (d2,s)= dDoc d1 x
dKinding d1 x = (d1,text (show x))

dLdata:: (Swap t,DocReady t,NameStore d) =>
         Quant -> d -> L([Pred],t) -> (d,Doc)
dLdata quant d1 args = (d4,PP.cat [prefix, eqsS,indent rhoS])
    where (trips,(eqs,rho)) = unsafeUnwind args
          (d2,prefix,indent) = tripf d1 trips
          (d3,eqsS) = feqs d2 eqs
          (d4,rhoS) = dDoc d3 rho
          sh All = text "forall "
          sh Ex  = text "exists "
          tripf d [] = (d,PP.empty,PP.nest 0)
          tripf d1 trips = (d2,sh quant <> (PP.cat argsStr) <> text ".",PP.nest 7)
            where (d2,argsStr) = thread pp (text " ") d1 trips
          feqs d [] = (d,PP.empty)
          feqs d [x::Pred] = (d1,s <> text " => ") where (d1,s) = dPred d x
          feqs d xs = (d1,PP.parens(PP.cat s) <> text " => ")
            where (d1,s) = thread dPred PP.comma d xs
          pp d2 (nm,MK k,q) =
            let (d3,name) = useStoreName nm (MK k) (prefix k) d2
                prefix (TcTv (Tv _ (Skol _) _)) s = (case q of {Ex -> "!"; All -> ""})++s
                prefix _ s = (case q of {Ex -> "_"; All -> ""})++s
            in case k of
                (Star LvZero) -> (d3,text name)
                _ -> let (d4,kind) = dKinding d3 k
                     in (d4,PP.parens(text name <> text "::" <> kind))

exSynListD :: forall t. (NameStore t) => t -> Tau -> (t,Doc)
exSynListD d (t@(TyApp (TyApp (TyCon ext _ c1 _) x) y))
     = (d2, PP.lbrack <> PP.cat ans <> text ("]"++postscript (synKey ext)))
  where (d2,ans) = f d t
        f d (TyApp (TyApp (TyCon ext' _ c1 _) x) y) | ext' == ext && listCons c1 ext =
          case y of
           (TyCon ext' _ c2 _) | ext' == ext && listNil c2 ext -> (d2,[w])
                   where (d2,w) = dTau d x
           (TyApp (TyApp (TyCon ext' _ c1 _) _) _) | ext' == ext && listCons c1 ext -> (d2,ans)
             where (d1,elem) = dTau d x
                   (d2,tail) = f d1 y
                   ans = (elem <> PP.comma): tail
           other -> (d2, [elem <> text "; ", ans])
             where (d1,elem) = dTau d x
                   (d2,ans) = dTau d1 other
exSynListD d t = (d,text ("Ill-formed List extension: "++sht t))

exSynLeftListD :: forall t. (NameStore t) => t -> Tau -> (t,Doc)
exSynLeftListD d (t@(TyApp (TyApp (TyCon ext _ c1 _) x) y))
     = (d2, PP.lbrack <> PP.cat ans <> text ("]"++postscript (synKey ext)))
  where (d2,ans) = f d t
        f d (TyApp (TyApp (TyCon ext' _ c1 _) x) y) | ext' == ext && leftListCons c1 ext =
          case x of
           (TyCon ext' _ c2 _) | ext' == ext && leftListNil c2 ext -> (d2,[w])
                   where (d2,w) = dTau d y
           (TyApp (TyApp (TyCon ext' _ c1 _) _) _) | ext' == ext && leftListCons c1 ext -> (d2,ans)
             where (d1,elem) = dTau d y
                   (d2,tail) = f d1 x
                   ans = tail ++ [PP.comma <> elem]
           other -> (d2, [ans <> text "; ", elem])
             where (d1,elem) = dTau d y
                   (d2,ans) = dTau d1 other
exSynLeftListD d t = (d,text ("Ill-formed LeftList extension: "++sht t))


exSynRecordD :: forall t. (NameStore t) => t -> Tau -> (t,Doc)
exSynRecordD d (t@(TyApp (TyApp (TyApp (TyCon ext _ c1 _) tag) x) y))
      = (d2, PP.lbrace <> PP.cat ans <> text ("}"++postscript (synKey ext)))
  where (d2,ans) = f d t
        f d (TyApp (TyApp (TyApp (TyCon ext' _ c1 _) tag) x) y) | ext' == ext && recordCons c1 ext =
          let (d0,tags) = dTau d tag
              (d1,elem) = dTau d0 x
          in case y of
              (TyCon ext' _ c2 _) | ext' == ext && recordNil c2 ext -> (d1,[tags <> PP.equals <> elem])
              (TyApp (TyApp (TyApp (TyCon ext' _ c1 _) _) _) _) | ext' == ext && recordCons c1 ext -> (d2,ans)
                where (d2,tail) = f d1 y
                      ans = (tags <> PP.equals <> elem <> PP.comma):tail
              other -> (d2,[tags <> PP.equals <> elem <> PP.semi,ans])
                where (d2,ans) = dTau d1 other
exSynRecordD d t = (d,text("Ill-formed Record extension: "++sht t))

exSynLeftRecordD :: forall t. (NameStore t) => t -> Tau -> (t,Doc)
exSynLeftRecordD d (t@(TyApp (TyApp (TyApp (TyCon ext _ c1 _) tag) x) y))
      = (d2, PP.lbrace <> PP.cat ans <> text ("}"++postscript (synKey ext)))
  where (d2,ans) = f d t
        f d (TyApp (TyApp (TyApp (TyCon ext' _ c1 _) x) tag) y) | ext' == ext && leftRecordCons c1 ext =
          let (d0,tags) = dTau d tag
              (d1,elem) = dTau d0 y
          in case x of
              (TyCon ext' _ c2 _) | ext' == ext && leftRecordNil c2 ext -> (d1,[tags <> PP.equals <> elem])
              (TyApp (TyApp (TyApp (TyCon ext' _ c1 _) _) _) _) | ext' == ext && leftRecordCons c1 ext -> (d2,ans)
                where (d2,tail) = f d1 x
                      ans = tail ++ [PP.comma <> tags <> PP.equals <> elem]
              other -> (d2,[ans, PP.semi <> tags <> PP.equals <> elem])
                where (d2,ans) = dTau d1 other
exSynLeftRecordD d t = (d,text("Ill-formed LeftRecord extension: "++sht t))


exSynPairD:: forall t. (NameStore t) => t -> Tau -> (t,Doc)
exSynPairD d (t@(TyApp (TyApp (TyCon ext' _ c1 _) x) y))
     = (d3, PP.lparen <> PP.cat ws <> text (")"++postscript (synKey ext')))
  where collect (TyApp (TyApp (TyCon ext _ c1 _) x) y) | ext == ext' && pairProd c1 ext = x : collect y
        collect (TyApp (TyApp (TyCon ext _ c1 _) x) y) | ext == ext' && leftPairProd c1 ext = collect x ++ [y]
        collect y = [y]
        (d1,x') = dTau d x
        (d2,y') = dTau d1 y
        (d3,ws) = thread dTau PP.comma d (collect t)

exSynItemD:: forall t. (NameStore t) => t -> Tau -> (t,Doc)
exSynItemD d (t@(TyApp (TyCon ext _ c1 _) x)) | itemItem c1 ext
     = (d1, PP.lparen <> x' <> text (")"++postscript (synKey ext)))
  where (d1,x') = dTau d x

dPar :: NameStore t => t -> Tau -> (t, Doc)
dPar xs z@(TyApp (TyCon sx _ "[]" _) x) = dTau xs z
dPar xs z@(TyApp (TyApp (TyCon sx _ "(,)" _) x) y) = dTau xs z
dPar xs z@(TyApp (TyApp (TyCon sx _ "(+)" _) x) y) = dTau xs z
dPar xs z@(TyApp (TyApp (TyCon lx _ c _) _) _) | listCons c lx  = dTau xs z
dPar xs z@(TyApp (TyApp (TyCon lx _ c _) _) _) | leftListCons c lx  = dTau xs z
dPar xs z@(TyApp (TyApp (TyApp (TyCon rx _ c _) _) _) _) | recordCons c rx = dTau xs z
dPar xs z@(TyApp (TyApp (TyApp (TyCon rx _ c _) _) _) _) | leftRecordCons c rx = dTau xs z
dPar xs z@(TyApp (TyApp (TyCon px _ c _) _) _) | pairProd c px = dTau xs z
dPar xs z@(TyApp (TyCon nx _ c _) _) | natSucc c nx = dTau xs z
dPar xs  z | isRow z = dTau xs z
dPar xs x@(Karr _ _) = (ys, PP.parens ans)
  where (ys,ans) = dTau xs x
dPar xs x@(TyApp _ _) = (ys, PP.parens ans)
  where (ys,ans) = dTau xs x
dPar xs x@(TySyn nm n fs as t) | n>=1 =  (ys, PP.parens ans)
  where (ys,ans) = dTau xs x
dPar xs x@(TyEx _) = (ys, PP.parens ans)
  where (ys,ans) = dTau xs x
dPar xs x = dTau xs x

dArrow :: NameStore t => t -> Tau -> (t, Doc)
dArrow xs (t@(TyApp (TyApp (TyCon sx _ "(->)" _) x) y)) = (ys, PP.parens z)
  where (ys,z) = dTau xs t
dArrow xs (t@(Karr _ _)) = (ys, PP.parens z)
  where (ys,z) = dTau xs t
dArrow xs x@(TyEx _) = (ys, PP.parens ans)
  where (ys,ans) = dTau xs x
dArrow xs t = dTau xs t

-- =======================================

-- Exhibit Tau
instance NameStore d => Exhibit d Tau where
  exhibit xs t = docToString (dTau xs t)

-- Exhibit Rho
instance NameStore d => Exhibit d Rho where
  exhibit xs t = docToString (dRho xs t)

-- Exhibit Sigma
instance NameStore d => Exhibit d Sigma where
  exhibit xs x = docToString (dSigma xs x)

-- Exhibit PolyKind
instance (NameStore d,Exhibit d Name) => Exhibit d PolyKind  where
  exhibit d1 x = docToString (dPoly d1 x)


instance NameStore d => Exhibit d Pred where
  exhibit d1 x = docToString (dPred d1 x)

instance (NameStore d,Exhibit d x) => Exhibit d (Expected x) where
  exhibit d1 (Check x) = exhibit d1 x
  exhibit d1 (Infer _) =(d1,"Infer Reference")

-- [(Tau,Tau)]
instance NameStore d => Exhibit d [(Tau,Tau)] where
  exhibit xs [] = (xs,"")
  exhibit xs ys = (zs,"("++ans++") => ")
    where (zs,ans) = exhibitL exhibitTT xs ys ", "

exhibitTT xs (x,y) = (zs,a++"="++b)
    where (ys,a) = exhibit xs x
          (zs,b) = exhibit ys y

instance NameStore d => Exhibit d [(TcTv,Tau)] where
  exhibit d ys = (d1,"{"++s++"}")
    where (d1,s) = f d ys
          f xs [] = (xs,"")
          f xs ys = exhibitL exhibitVT xs ys ", "

exhibitVT xs (x,y) = (zs,a++"="++b)
    where (ys,a) = exhibitTv xs x
          (zs,b) = exhibit ys y

instance Exhibit d x => Exhibit d (Maybe x) where
  exhibit d Nothing = (d,"Nothing")
  exhibit d (Just x) = (d1,"(Just "++s++")") where (d1,s) = exhibit d x

-- [Pred]
instance NameStore d => Exhibit d [Pred] where
  exhibit xs [] = (xs,"")
  exhibit xs ys = exhibitL exhibit xs ys ", "

instance NameStore d => Exhibit d [PPred] where
  exhibit xs [] = (xs,"")
  exhibit xs ys = exhibitL exhibit xs ys ", "

------------------------------------------------
-- Make Display instances

instance Exhibit (DispInfo Z) t => Display t Z where
  disp = exhibit

-------------------------------------------------
-- Make Alpha instances

class Alpha t where
  alpha :: [(Name,String)] -> t -> String

instance Exhibit [(Name,String)] t => Alpha t where
  alpha disp x = y where (disp2,y) = exhibit disp x

pprint :: Exhibit (DispInfo Z) b => b -> [Char]
pprint x = s
 where (d2,s) = exhibit (disp0:: DispInfo Z) x

------------------------------------------------------------
-- Turn types into PT in order to render them with indentation

toPT :: Exhibit a Tau => a -> Tau -> (a,PT)
toPT d (TyVar nm k) = (d2,TyVar' s) where (d2,s) = useStoreName nm k ("'"++) d
toPT d (TyApp (TyApp (TyCon sx n "(->)" k) x) y) = (d2,Rarrow' a b)
  where (d1,a) = toPT d x
        (d2,b) = toPT d1 y
toPT d (TyApp x y) = (d2,TyApp' a b)
  where (d1,a) = toPT d x
        (d2,b) = toPT d1 y
toPT d (TyCon sx l s k) = (d,TyCon' s Nothing) -- FIXPT
toPT d (Star n) =
  case fromLevel n of
    Just m -> (d,Star' m Nothing)
    Nothing -> (d,Star' 0 (Just (show n)))
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

toPPred :: NameStore t => t -> Pred -> (t, PPred)
toPPred d (Equality x y) = (d2,Equality' a b)
  where (d1,a) = toPT d x
        (d2,b) = toPT d1 y
toPPred d (Rel x) = (d1,Rel' "" a) where (d1,a) = toPT d x

toTrip :: NameStore t => t -> (Name, Kind, Quant) -> (t, (String, PT, Quant))
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
rho2PT d (Rsum x y) = (d2,(TyApp' (TyApp' (TyCon' "(,)" Nothing) a) b))
  where (d1,a) = sigma2PT d x
        (d2,b) = sigma2PT d1 y
rho2PT d (Rpair x y) = (d2,(TyApp' (TyApp' (TyCon' "(+)" Nothing) a) b))
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
  show (K lvs x) = (if null lvs then "(" else "(level "++vs++" . ")++y ++")"
   where (disp2,y) = exhibit () x
         vs = plist "" lvs " " ""

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

-----------------------------------------------------

solveHP ::  TyCh m => (String,Rho) -> [Pred] -> [Pred] -> m ([Pred],Unifier2)
solveHP context@(s,r) truths oblig =
  do { truths2 <- zonk truths
     ; oblig2 <- zonk oblig
     ; let (hotruths,fots) = span higherOrder truths2
           force (1,u) = mutVarSolve u
           force (n,u) = return []
     ; counts <- mapM (countM oblig2) hotruths
     ; mapM force counts
     ; truths3 <- zonk truths2
     ; oblig3 <- zonk oblig2
     -- ; warn [Ds "Calling Solve inside solveHP ",Dd oblig3]
     ; setTruths truths3 (solveSomeEqs ("3."++s,r) oblig3)
     }


-- When we map "matchRel p" over a list we get a list of (count,unifier).
-- Interpret this as (1,unifier) if "p"  matches and (0,[]) if it doesn't.
-- "sumM"ing up such a list we get (number_of_matches,first_unifier)
-- if it is (1,unifier) then there was exactly 1 match and unifier
-- comes from that match. For those with exactly 1 match, we can force
-- the unification to take place, by using solveMutVars.

sumM :: [(Int,[a])] -> (Int,[a])
sumM [] = (0,[])
sumM ((n,xs):zs) = (n+m,xs) where (m,_) = sumM zs

matchRel (Rel p) (Rel q) =
  do {ans <- mguB [(p,q)]
     ; case ans of
         Left (_,u) -> return (1,u)
         Right (a,b,c) -> return (0,[])}
matchRel p q = return(0,[])

countM ps p = do { ans <- mapM (matchRel p) ps
                 ; return(sumM ans)}

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
-- 1) Equalities that are Mutvar solvable,
-- 2) Equalities that are Easy narrowing (it looks easy at least),
-- 3) Equalities that are hard to narrow,
-- 4) Other kinds of predicates.
--
-- 1) Mutvar solvable look like (Equal x type),
-- where on side is a variable, except where x = skol
-- or y={plus y z}, i.e. a TyFun where the var (y) occurs
-- in the other side, like the y in  {plus y z}.
--
-- 2) Easy ones include (Equal Z {plus n n}) where one
-- side is a ground term. They look easy, but they might be hard.
-- One can't tell without trying, but it is worth trying.
--
-- 3) Hard is all other equalities like (Equal x {plus a b})
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

splitClass (TcTv (Tv un (Skol _) k)) any = Hard
splitClass any (TcTv (Tv un (Skol _) k)) = Hard
splitClass (TcTv x) (y@(TyFun _ _ _)) | all (/=x) (tvsTau y) = MutSolve
splitClass (TcTv _) (TyFun _ _ _) = Hard
splitClass (y@(TyFun _ _ _)) (TcTv x) | all (/=x) (tvsTau y) = MutSolve
splitClass (TyFun _ _ _) (TcTv _) = Hard
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
     ; hard2 <- sub ([],unifier,[],[]) hard
     ; easy2 <- sub ([],unifier,[],[]) easy
     ; other2 <- sub ([],unifier,[],[]) other
     ; return(other2,hard2,easy2,unifier)}

-- To add a list of bindings to the mutable unifier, run down
-- the list overwriting the ref cells for each mutable type var.
-- We use unify (rather than unifyVar) because unification in
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
     ; let env = ([],unifier,[],[])
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

-- mguStarVar is only called from mguStar
--
mguStarVar :: TyCh m => (IO String, Loc)
                    -> [TcTv]
                    -> TcTv
                    -> Tau
                    -> [(Tau, Tau)]
                    -> m (Either ([(TcTv, Tau)], [Pred]) (String, Tau, Tau))
mguStarVar str beta (x@(Tv n _ _)) (tau@(TyFun _ _ _)) xs | elem x (tvsTau tau)  =
  do { norm <- normTyFun tau
     ; case norm of
       Just (TcTv (Tv m _ _)) | n==m -> mguStar str beta xs
       Just tau' -> if elem x (tvsTau tau')
                    then return(Right("occurs check (after normalization)", TcTv x, tau'))
                    else mguStarVar str beta x tau' xs
       _ -> return(Right("occurs check (not normalizable)", TcTv x, tau))
     }
mguStarVar str beta (x@(Tv _ _ (MK k))) tau xs =
  do { let vs = tvsTau tau
           new1 = [(x,tau)]
     ; k2 <- kindOfM tau
     ; new2 <- mguStar str beta (subPairs new1 ((k,k2):xs))
     ; return(if elem x vs
              then Right("occurs check", TcTv x, tau)
              else composeStar new2 new1)}

whichPat (Tv u (Rigid q loc (str,ref)) k) = str
whichPat _ = "?"

mguStar:: TyCh m => (IO String,Loc) -> [TcTv] -> [(Tau,Tau)] -> m(Either ([(TcTv,Tau)],[Pred]) (String,Tau,Tau))
mguStar str beta [] = return(Left ([],[]))
mguStar str beta ((TcTv (Tv n _ _),TcTv (Tv m _ _)):xs) | n==m
   = mguStar str beta xs
mguStar str beta ((TcTv a,TcTv b):xs) | elem a beta && not(elem b beta)
   = mguStarVar str beta a (TcTv b) xs
mguStar str beta ((TcTv b,TcTv a):xs) | elem a beta && not(elem b beta)
   = mguStarVar str beta a (TcTv b) xs


mguStar (str,loc) beta ((TcTv (a@(Tv _ _ k)),TcTv b):xs)
   | (elem a beta && elem b beta) || (not(elem a beta) && not(elem b beta))
   = do { info <- showMdisp [Ds "\nvia the 'common rule' from ",Dd a,Ds " and ",Dd b]
        ; let description = do { x <- str; return(x++info)}
        ; cVar <- newRigidTyVar All loc description k
        ; let c = TcTv cVar
        ; let new1 = [(a,c),(b,c)]
        ; new2 <- mguStar (str,loc) beta (subPairs new1 xs)
        ; return(composeStar new2 new1)}


mguStar str beta ((TcTv a,tau):xs) = mguStarVar str beta a tau xs
mguStar str beta ((tau,TcTv a):xs) = mguStarVar str beta a tau xs
mguStar str beta ((TyApp x y,TyApp a b):xs) = mguStar str beta ((x,a):(y,b):xs)
mguStar str beta ((TyCon sx level_ s1 _,TyCon tx level_2 s2 _):xs) | s1==s2 = mguStar str beta xs -- TODO LEVEL
mguStar str beta ((Star n,Star m):xs) = unifyLevel "mguStar" n m >> mguStar str beta xs
mguStar str beta ((Karr x y,Karr a b):xs) = mguStar str beta ((x,a):(y,b):xs)
mguStar str beta ((TySyn nm n fs as x,y):xs) = mguStar str beta ((x,y):xs)
mguStar str beta ((y,TySyn nm n fs as x):xs) = mguStar str beta ((y,x):xs)

mguStar str beta ((x@(TyFun f _ ys),y@(TyFun g _ zs)):xs) | f==g =
  eitherM (mguStar str beta (zip ys zs))
     (\ (old,ps) -> eitherM (mguStar str beta (subPairs old xs))
                      (\ (new,qs) -> return(composeStar  (Left(new,ps++qs)) old))
                      (\ err -> return(Right err)))
     (\ _ -> do { ans <- (mguStar str beta xs); return (emitStar (x,y) ans) })

mguStar str beta ((x@(TyFun f _ ys),y):xs) =
   do { ans <-  (mguStar str beta xs); return (emitStar (x,y) ans) }
mguStar str beta ((y,x@(TyFun f _ ys)):xs) =
   do { ans <-  (mguStar str beta xs); return (emitStar (y,x) ans) }
mguStar str beta ((x,y):xs) = return(Right("No Match", x, y))



morepolySS:: TyCh m => [TcTv] -> Sigma -> Sigma -> m(Either ([(TcTv,Tau)],[Pred]) (String,Tau,Tau))
morepolySS beta sigma1 sigma2 =
  do { (skol_tvs,truths,rho) <- rigidInstance (subsumeInj sigma1 sigma2) (show sigma2) (K [] sigma2)
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

subsumeInj s1 s2 rho = return("Subsumption check on "++show s1++" <= "++show s2++" where skolem "++show rho)

string2Tau s = TyCon Ox (lv 0) s (K [](simpleSigma (Star LvZero)))


morepolySR:: TyCh m => [TcTv] -> Sigma -> Rho -> m(Either ([(TcTv,Tau)],[Pred]) (String,Tau,Tau))
morepolySR beta (Forall(Nil([],rho1))) rho2 = morepolyRR beta rho1 rho2
morepolySR beta sigma1 rho2 =
     do { (vs,preds,rho1) <- rigidInstance (subsumeInj sigma1 rho2) (show sigma1) (K [] sigma1) -- instanL sig
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
  f (Rtau x) (Rtau y) = mguStar (return "morepolyRR",Z) s [(x,y)]


-- showKinds

subtermsTau:: Tau -> [Tau] -> [Tau]
subtermsTau (v@(TyVar nm k)) ans = if elem v ans then ans else v:ans
subtermsTau (x@(TyApp _ _)) ans = x : foldr subtermsTau ans args
  where (f,args) = rootTau x []
subtermsTau (x@(TyCon ext l nm k)) ans = if nullCon x then x:ans else ans
subtermsTau (Star n) ans = ans
subtermsTau (Karr x y) ans = subtermsTau x (subtermsTau y (Karr x y : ans))
subtermsTau (TyFun nm k ts) ans = foldr subtermsTau (TyFun nm k ts : ans) ts
subtermsTau (TcTv x) ans = ans
subtermsTau (TySyn nm n ks args t) ans = subtermsTau t ans
subtermsTau (TyEx _) ans = ans

nullCon :: Tau -> Bool
nullCon (TyCon _ _ _ (K _ (Forall l))) = nonarrow t
  where (args,(preds,t)) = unsafeUnwind l
        nonarrow (Rarrow _ _) = False
        nonarrow (Rtau (TyApp (TyApp (TyCon _ _ "(->)" _) x) y)) = False
        nonarrow (Rtau (Karr x y)) = False
        nonarrow x = True
nullCon _ = False

subtermsRho:: Rho -> [Tau] -> [Tau]
subtermsRho (Rarrow x y) ans = subtermsSigma x (subtermsRho y ans)
subtermsRho (Rpair x y) ans = subtermsSigma x (subtermsSigma y ans)
subtermsRho (Rsum x y) ans = subtermsSigma x (subtermsSigma y ans)
subtermsRho (Rtau x) ans = subtermsTau x ans

subtermsSigma:: Sigma -> [Tau] -> [Tau]
subtermsSigma (Forall l) ans = subtermsRho rho ans
  where (args,(preds,rho)) = unsafeUnwind l


------------------------------------------------------------------

