-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Thu Mar  3 11:15:06 Pacific Standard Time 2005
-- Omega Interpreter: version 1.0

module RankN where

import Bind
import IOExts
import Monads
import Monad(when,foldM)
import List((\\),nub,union,sortBy,groupBy)
import Auxillary(Loc(..),plist,plistf,extendM,foldrM,makeNames
                ,DispInfo(..),Display(..),useDisplay,initDI
                ,disp2,disp3,disp4,disp5,dispL)
import ParserAll  -- This for defining the parser for types
-- To import ParserAll you must define CommentDef.hs and TokenDef.hs
-- These should be in the same directory as this file.

--------------------------------------------------------------------
type Uniq = Integer
type TRef = IORef (Maybe Tau)
data Eqn = Equality Tau Tau

data PolyKind = K Sigma -- some Type Constrs have polymorphic kinds!
data Kind = MK Tau

data L x = Nil x | Cons (Kind,Quant) (Bind Name (L x))
data Sigma = Forall (L ([Eqn],Rho))

data Rho
  = Rarrow Sigma Rho
  | Rpair Sigma Sigma
  | Rsum Sigma Sigma
  | Rtau Tau

data Tau
  = TyVar Name Kind
  | TyApp Tau Tau
  | TyCon String PolyKind
  | Star Int
  | Karr Tau Tau
  | TyFun String PolyKind [Tau]
  | TcTv TcTv
     
data Flavor = Flexi TRef | Rigid Quant Loc String | Skol String

data TcTv = Tv Uniq Flavor Kind

data Expected a = Infer (IORef a) | Check a

data Quant = Ex | All deriving Show

instance Eq TcTv where (Tv i _ _) == (Tv j _ _) = i==j

instance Ord TcTv where compare (Tv i _ _) (Tv j _ _) = compare i j

type MGU = [(TcTv,Tau)]

---------------------------------------------------------------
-- Class definitions

class (HasIORef m,Fresh m,HasNext m,Accumulates m Eqn
      ,TracksLoc m,HasOutput m) => TyCh m where
  envTvs :: m [(String,Sigma,[TcTv])] -- extract free type vars 
  handleM :: Int -> m a -> (DispInfo -> String -> m a) -> m a
  assume :: MGU -> m a -> m a
  getAssume :: m MGU
  getDisplay :: m DispInfo
  normform :: Tau -> m Tau

-- A type is TypeLike if it supports a few primitive operations
-- substitution, zonking, and finding the free type variables.

type ForAllArgs = [(Name,Kind,Quant)]

class TyCh m => TypeLike m t where
  sub :: ([(Name,Tau)],[(TcTv,Tau)],[(String,Tau)]) -> t -> m t
  zonk :: t -> m t
  get_tvs :: t -> m [ TcTv ]
  for_all :: ForAllArgs -> t -> m Sigma
  nf :: t -> m t

subst env t = sub (env,[],[]) t


-- A pair of types can be in the subsumption class if we can
-- ask if one is more polymorphic than another.

class TyCh m => Subsumption m x y where
  morepoly :: x -> y -> m ()

-- a term type is Typable if one can check and infer types for it.
-- This is really a binary relation since the sort of "ty"
-- could be several things: like Rho, Sigma, or Kind

class TyCh m => Typable m term ty where
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
  infer t = do { ref <- newRef (error "infer: no result")
               ; s <- tc t (Infer ref)
               ; t' <- readRef ref
               ; return(t',s)
               }
  tc x (Check t) = check x t
  tc x (Infer ref) =
     do { (ty,x') <- infer x; writeRef ref ty; return x'}


-- check that a list of terms all have the same expected type.

tcL :: Typable m term ty => [term] -> Expected ty -> m [term]
tcL [] expect = return []
tcL (t:ts) expect =
   do { t2 <- tc t expect; ts2 <- tcL ts expect; return(t2:ts2) }

checkL terms ty = tcL terms (Check ty)


-- check that a list of terms all match a multiple arg function type
-- checkArgs [t1,t2,t3] (a -> b -> c -> d) last ==> 
-- tc t1 a; tc t2 b; tc t3 c; morepoly last d

checkArgs :: Typable m term Sigma => [term] -> Rho -> Expected Rho -> m [term]
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

star = MK(Star 0)
starR = Rtau(Star 0)
karr (MK x) (MK y) = MK(Karr x y) 

star_star = star `karr` star
star1 = MK(Star 1)
poly :: Kind -> PolyKind
poly (MK t) = K(simpleSigma t)

unpoly :: PolyKind -> Kind
unpoly (K (Forall (Nil([],Rtau tau)))) = MK tau
unpoly x = error ("Can't turn the polykind "++show x++" into a normal kind.")

intT =    TyCon "Int" (poly star)
charT =   TyCon "Char" (poly star)
boolT =   TyCon "Bool" (poly star)
listT =   TyCon "[]" (poly star_star)
parserT = TyCon "Parser" (poly star_star)
unitT =   TyCon "()" (poly star)
symbolT = TyCon "Symbol" (poly star)
atomT =   TyCon "Atom" kind4Atom
maybeT =  TyCon "Maybe" (poly star_star)
monadT =  TyCon "Monad" (poly (karr (star_star) star))
pairT =   TyCon "(,)" (poly (karr star (star_star)))
sumT =    TyCon "(+)" (poly (karr star (star_star)))
codeT =   TyCon "Code" (poly star_star)
ioT =     TyCon "IO" (poly star_star)
ptrT =    TyCon "Ptr" (poly star_star)
arrowT =  TyCon "(->)" (poly (karr star (star_star)))
eqT =     TyCon "Equal" kind4Eq
hiddenT = TyCon "Hidden" kind4Hidden
chrSeqT = TyCon "ChrSeq" (poly star)
floatT = TyCon "Float" (poly star)
bindT =   TyCon "Bind" (poly (karr star (star_star)))
stringT = TyApp listT charT

type ToEnv = [(String,Tau,PolyKind)]

toEnv0 :: ToEnv
toEnv0 = 
  [( "Int"    , intT, poly star)
  ,( "Char"   , charT, poly star)
  ,( "Float"  , floatT, poly star)
  ,( "ChrSeq" , chrSeqT, poly star)
  ,( "Bool"   , boolT, poly star)
  ,( "Maybe"  , maybeT, poly star_star)
  ,( "Monad"  , monadT, poly (karr (star_star) star))
  ,( "[]"     , listT,poly star_star)
  ,( "Parser" , parserT,poly star_star)
  ,( "(,)"    , pairT, poly (karr star (star_star)))
  ,( "()"     , unitT, poly star)
  ,( "(->)"   , arrowT, poly (karr star (star_star)))
  ,( "Symbol" , symbolT, poly star)
  ,( "Atom"   , atomT, kind4Atom)
  ,( "(+)" , sumT, poly (karr star (star_star)))
  ,( "Code" , codeT, poly star_star)
  ,( "IO" , ioT, poly star_star)
  ,( "Ptr" , ptrT,poly star_star)
  ,( "Equal" , eqT, kind4Eq)
  ,( "Hidden" , hiddenT, kind4Hidden)
  ,( "Bind", bindT,(poly (karr star (star_star))))
  ,( "String",stringT,poly star)
  --,( "plus",TyCon "plus" (poly star), poly star)
  ]

trans0 s = (readName "In trans0: ") toEnv0 s   
 
readName mess [] s = fail (mess++" unknown type: "++s)
readName mess ((x,tau,k):xs) s = if s==x then return tau else readName mess xs s
 
kind4Hidden :: PolyKind -- Hidden :: (forall (k:*1) . (k -> *0) -> *0)
kind4Hidden = K(Forall (Cons (star1,All) (bind name1 (Nil ([],ty)))))
   where k = TyVar name1 star1
         ty = Rtau((k `Karr` (Star 0)) `Karr` (Star 0))

kind4Eq :: PolyKind -- Eq :: (forall (k:*1) . k -> k -> *0)
kind4Eq = K(Forall (Cons (star1,All) (bind name1 (Nil ([],ty)))))
   where k = TyVar name1 star1
         ty = Rtau(k `Karr` (k `Karr` (Star 0)))

kind4Atom :: PolyKind -- Atom :: forall k: *1) . k -> *
kind4Atom = K(Forall (Cons (star1,All) (bind name1 (Nil ([],ty)))))
   where k = TyVar name1 star1
         ty = Rtau(k `Karr` (Star 0))


runType = Forall (Cons (star,All)
           (bind name1 (Nil ([],arrow (Forall (Nil ([],tcode a))) a))))
   where a = (Rtau(TyVar name1 star))

liftType = Forall (Cons (star,All)
           (bind name1 (Nil ([],arrow (Forall (Nil ([],a))) (tcode a)))))
   where a = (Rtau(TyVar name1 star))

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


tprods [t] = t
tprods (x:xs) = tpair x (tprods xs)

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
bindtype m = toSigma env (pt "forall a b . m a -> (a -> m b) -> m b")
  where env = [("m",m,poly star_star)]

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
         star1 = MK (Star 1)
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
  swaps cs (x@(TyCon "(->)" _)) = x  -- Never pull on the kind of (->)
  swaps cs (TyCon s k) = TyCon s (swaps cs k)
  swaps cs (Star n) = Star n
  swaps cs (Karr x y) = Karr (swaps cs x) (swaps cs y)
  swaps cs (TyFun nm k x) = TyFun (swaps cs nm) (swaps cs k) (swaps cs x)
  swaps cs (TcTv (Tv unq ref k)) = TcTv(Tv unq ref (swaps cs k))
      -- invariant, no type variable will ever bind to something with a TyVar
      -- otherwise we'd have to know how to swap over an IORef

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

instance Swap Eqn where
  swaps [] x = x
  swaps cs (Equality x y) = Equality (swaps cs x) (swaps cs y)

-------------------------------------------------------------
-- Typelike instances

fromMaybe x Nothing = x
fromMaybe x (Just w) = w

binaryLift f a b = do { x <- a; y <- b; return(f x y)}

-- TypeLike Tau
instance TyCh m => TypeLike m Tau where
  sub env@(ns,vs,cs) x = do { y <- prune x; f y}
    where f (TyVar nm k) =
            do { k2 <- sub env k
               ; return(fromMaybe (TyVar nm k2) (lookup nm ns))}
          f (TyApp x y) =  binaryLift TyApp (sub env x) (sub env y)
          f (TyCon s k) =
            do { k2 <- sub env k
               ; return(fromMaybe (TyCon s k2) (lookup s cs))}
          f (Star n) = return(Star n)
          f (Karr x y) =  binaryLift Karr (sub env x) (sub env y)
          f (TyFun nm k x) = do { y <- sub env x; k' <- sub env k; return(TyFun nm k' y) }
          f (TcTv x) = return(fromMaybe (TcTv x) (lookup x vs))
  zonk x = do { y <- prune x; f y}
    where f (TyVar nm k) = do { k2 <- zonk k; return(TyVar nm k2)}
          f (TyApp x y) =  binaryLift TyApp (zonk x) (zonk y)
          f (TyCon s k) =  do { k2 <- zonk k; return(TyCon s k2) }
          f (Star n) = return(Star n)
          f (Karr x y) =  binaryLift Karr (zonk x) (zonk y)
          f (TyFun nm k x) =  do { y <- zonk x; k' <- zonk k; return(TyFun nm k' y) }
          f (typ @(TcTv x)) = return typ
  get_tvs x = do { y <- prune x; f y}
    where f (TcTv (x@(Tv unq _ k))) = binaryLift union (get_tvs k) (return [x])
          f (TyApp x y) = binaryLift (union) (get_tvs x) (get_tvs y)
          f (Karr x y) = binaryLift (union) (get_tvs x) (get_tvs y)
          f (TyFun nm k x) = binaryLift union (get_tvs k) (get_tvs x)
          f (Star _) = return []
          f (TyCon s k) = get_tvs k
          f (TyVar nm k) = get_tvs k
  nf x = nfTau x                                          
  for_all xs r = return(Forall(windup xs ([],Rtau r)))

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

  get_tvs (Rarrow x y) = binaryLift (union) (get_tvs x) (get_tvs y)
  get_tvs (Rsum x y) = binaryLift (union) (get_tvs x) (get_tvs y)
  get_tvs (Rpair x y) = binaryLift (union) (get_tvs x) (get_tvs y)
  get_tvs (Rtau x) = get_tvs x
  for_all xs t = return(Forall(windup xs ([],t)))  
  nf x = nfRho x
  
-- TypeLike Sigma
instance  TyCh m => TypeLike m Sigma where
  sub env (Forall xs) = do { w <- sub env xs; return(Forall w)}
  zonk (Forall b) = do { w <- zonk b; return(Forall w)}
  get_tvs (Forall b) = get_tvs b
  for_all xs (Forall ys)  = return(Forall (addToL xs ys))
  nf x = nfSigma x
  
-- TypeLike PolyKind
instance  TyCh m => TypeLike m PolyKind where
  sub env (K r) = do { r' <- sub env r; return(K r')}
  zonk (K r) = do { r' <- zonk r; return(K r')}
  get_tvs (K r) = get_tvs r
  for_all xs (K s) = for_all xs s
  nf (K x) = do { z <- nfSigma x; return(K z) }
  
-- TypeLike Kind
instance  TyCh m => TypeLike m Kind where
  sub env (MK r) = do { r' <- sub env r; return(MK r')}
  zonk (MK r) = do { r' <- zonk r; return(MK r')}
  get_tvs (MK r) = get_tvs r
  for_all xs (MK r) = for_all xs r
  nf (MK x) = do { z <- nfTau x; return(MK z) }

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
      do { (nm,r) <- unbind b; binaryLift union (get_tvs k) (get_tvs r) }
  for_all xs l = fail "Can't apply for_all to an L list"

-- TypeLike []  i.e. Lists
instance TypeLike m t => TypeLike m [t] where
  sub env ts = mapM (sub env) ts
  zonk ts = mapM zonk ts
  get_tvs ts = do { vss <- mapM get_tvs ts; return(nub(concat vss)) }
  for_all xs r = fail "Can't Abstract over a list."
  nf x = mapM nf x


instance TyCh m => TypeLike m ([Eqn],Rho) where
  sub env (zs,r) = do { zs' <- mapM f zs; a <- sub env r; return(zs',a)}
          where f (Equality x y) = do { m <- sub env x; n <- sub env y; return(Equality m n)}
  zonk (zs,r) = do { zs' <- mapM f zs; a <- zonk r; return(zs',a)}
          where f (Equality x y) = do { m <- zonk x; n <- zonk y; return(Equality m n)}
  get_tvs (zs,r) = binaryLift union (get_tvs r) (foldrM f [] zs)
          where f (Equality x y) vs = do { as <- get_tvs x; bs <- get_tvs y; return(union as (union bs vs))}
  for_all xs r = return(Forall (windup xs r))
  nf (x,y) = binaryLift (,) (nfEqns x) (nfRho y)

instance TyCh m => TypeLike m (Tau,Tau) where
  sub env (x,y) = do { a <- sub env x; b <- sub env y; return(a,b)}
  zonk (x,y) = do { a <- zonk x; b <- zonk y; return(a,b)}
  get_tvs (x,y) = binaryLift union (get_tvs x) (get_tvs y)
  for_all xs r = fail "Can't Abstract over a pair of Tau"
  nf (x,y) = binaryLift (,) (nfTau x) (nfTau y)
  
instance TyCh m => TypeLike m Eqn where
  sub env (Equality x y) = do { a <- sub env x; b <- sub env y; return(Equality a b)}
  zonk (Equality x y) = do { a <- zonk x; b <- zonk y; return(Equality a b)}
  get_tvs (Equality x y) = binaryLift union (get_tvs x) (get_tvs y)
  for_all xs r = fail "Can't Abstract over a pair of Tau"
  nf (Equality x y) = binaryLift Equality (nfTau x) (nfTau y)  
  
instance TyCh m => TypeLike m (TcTv,Tau) where
  sub env (x,y) = do { a <- sub env y; return(x,a)}
  zonk (x,y) = do { b <- zonk y; return(x,b)}
  get_tvs (x,y) = (get_tvs y)
  for_all xs r = fail "Can't Abstract over a pair of (TcTv,Tau)"
  nf (x,y) = do { w <- nfTau y; return(x,w) }


---------------------------------------------------------------------
-- unify tries to unify to Tau types, This enforces that you can't
-- unify embedded Foralls, or TyVars which only occur inside Foralls

prune :: TyCh m => Tau -> m Tau
prune (typ @ (TcTv (v @ (Tv uniq (Rigid _ _ _) k)))) = 
  do { theta <- getAssume
     ; case lookup v theta of
         Just new -> prune new
         Nothing -> return typ }
prune (typ @ (TcTv (Tv uniq (Flexi ref) k))) =
  do { maybet <- readRef ref
     ; case maybet of
         Nothing -> return typ
         Just t -> do{t2 <- prune t; writeRef ref (Just t2); return t2}}
prune t = return t


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
        f (x@(TyCon s _)) (y@(TyCon t _)) =
           if s==t then return () else matchErr "different constants" x y
        f (x@(Star n)) (y@(Star m)) = 
           if n==m then return () else matchErr "different level" x y  
        f (Karr x y) (Karr a b) = do { unify x a; unify y b }
        f (TcTv x) t = unifyVar x t
        f t (TcTv x) = unifyVar x t 
        f (x@(TyFun nm k _)) y = emit x y
	f y (x@(TyFun nm k _)) = emit x y
        f s t = matchErr "different types" s t

emit x y = do { a <- zonk x; b <- zonk y; injectAccum [Equality a b]}

unifyVar (x@(Tv u1 r1 k1)) (t@(TcTv (Tv u2 r2 k2))) | u1==u2 = return ()
unifyVar (x@(Tv u1 (Flexi r1) (MK k))) t =
  do { vs <- get_tvs t
     ; t2 <- zonk t
     ; when (any (==x) vs) (matchErr "Occurs check" (TcTv x) t2)
     ; (new_t) <- handleM 1 (check t k) (kinderr t k u1)
     ; writeRef r1 (Just t2)
     ; return ()
     }
unifyVar (x@(Tv _ (Rigid _ _ _) _)) (TcTv v@(Tv _ (Flexi _) _)) = unifyVar v (TcTv x) 
unifyVar (x@(Tv _ (Skol s) _))      (TcTv v@(Tv u2 r2 k2))      = unifyVar v (TcTv x)
unifyVar v (x@(TyFun nm k _)) = emit (TcTv v) x
unifyVar v t = matchErr "(V) different types" (TcTv v) t
     
       
matchErr s t1 t2 = failP 0 d1 (s++"\n   "++dt1++" =/= "++dt2++"\n"++show(t1,t2))
 where (d1,dt1,dt2) = disp2 initDI (t1,t2)

kinderr t k u1 d1 s = 
   failP 0 d2 ("Type: "++ts++"\ndoes not have kind: "++ks ++s++"\n var = "++us)
 where (d2,ts,ks,us) = disp3 d1 (t,k,u1)                            

-----------------------------------------
-- Force a Rho type to have an Rarrow shape, a Pair shape, a Sum shape

unifyFun :: TyCh m => Rho -> m (Sigma,Rho)
unifyFun (Rarrow x y) = return (x,y)
unifyFun (Rtau (TyApp (TyApp z@(TyCon "(->)" doNotPullThis) x) y)) = 
   return(Forall (Nil ([],Rtau x)) ,Rtau y)
unifyFun (Rtau x) = 
   do { a <- newTau star  
      ; b <- newTau star  
      ; unify x (tarr a b)
      ; a1 <- zonk a
      ; b1 <- zonk b
      ; return (simpleSigma a1,Rtau b1) }
unifyFun x = fail ("Expected an function type: "++show x)      


unifyCode :: TyCh a => Expected Rho -> a Rho
unifyCode (Check (Rtau (TyApp (TyCon "Code" k) a))) = return (Rtau a)
unifyCode expected =
  do { a <- newRho star; zap a (tcode a) expected }


sigmaPair :: TyCh m => Sigma -> m (Sigma,Sigma)
sigmaPair (Forall (Nil ([],Rpair x y))) = return (x,x)
sigmaPair (Forall (Nil (eqs,Rpair x y))) = return (x,x)
sigmaPair (Forall (Nil (eqs,Rtau x))) =
   do { a <- newTau star; b <- newTau star
      ; unify x (tpair a b); 
      ; z1 <- zonk a; z2 <- zonk b
      ; return(mediumSigma eqs z1, mediumSigma eqs z2)}
sigmaPair (Forall (Cons (k,q) b)) =
   do { (nm,l) <- unbind b
      ; outputString ("name = "++show nm++" l = "++show (Forall l))
      ; (Forall a,Forall b) <- sigmaPair (Forall l)
      ; outputString ("A = "++show(Forall a)++" B = "++show (Forall b))
      ; return(Forall (Cons (k,q) (bind nm a))
              ,Forall (Cons (k,q) (bind nm b)))
      }

sigmaSum :: TyCh m => Sigma -> m (Sigma,Sigma)
sigmaSum (Forall (Nil (_,Rsum x y))) = return (x,x)
sigmaSum (Forall (Nil (_,Rtau x))) =
   do { a <- newTau star; b <- newTau star
      ; unify x (tsum a b); return(simpleSigma a, simpleSigma b)}
sigmaSum (Forall (Cons (k,q) b)) =
   do { (nm,l) <- unbind b
      ; (Forall a,Forall b) <- sigmaSum (Forall l)
      ; return(Forall (Cons (k,q) (bind nm a))
              ,Forall (Cons (k,q) (bind nm b)))
      }

expecting :: 
  TyCh m => String -> (Tau -> Tau -> Tau) -> Expected Rho -> m (Rho,Rho)
expecting shape f expect =
  do { a <- newTau star; b <- newTau star
     ; case expect of
         Check (Rtau p) -> unify p (f a b)
         Infer ref -> writeRef ref (Rtau (f a b))
         Check other -> fail ("Expecting a "++shape++": "++show other)
     ; return(Rtau a,Rtau b) }

---------------------------------------------------------------------
-- create new fresh variables and types

newFlexiTyVar :: TyCh m => Kind -> m TcTv
newFlexiTyVar k =
  do { n <- nextInteger; r <- newRef Nothing; return(Tv n (Flexi r) k) }

newRigidTyVar :: TyCh m => Quant -> Loc -> String -> Kind -> m TcTv
newRigidTyVar q loc s k =
  do { n <- nextInteger; return(Tv n (Rigid q loc s) k) }

newSkolTyVar :: TyCh m => String -> Kind -> m TcTv
newSkolTyVar s k =
  do { n <- nextInteger; return(Tv n (Skol s) k) }


newTau k = do { v <- newFlexiTyVar k; return (TcTv v)}
newRho k = do { v <- newTau k; return(Rtau v)}
newSigma k = do { v <- newTau k; return (simpleSigma v)}

newKind k = do { v <- newTau k; return (MK v) }

simpleSigma tau = Forall (Nil ([],Rtau tau))
mediumSigma eqs tau = Forall (Nil (eqs,Rtau tau))

--------------------------------------------------------------------
-- Instantiation. Turn a Sigma into a Rho by instantiating its vars,

-- every var a Rigid var
skolTy :: TyCh m => Sigma -> m ([TcTv],[Eqn],Rho)
skolTy sigma = unBindWith new sigma
   where new nam quant k = do {v <- newSkolTyVar (show nam) k; return(TcTv v)}

-- every var a Flexi var, and apply the substitution implied by the equations
instanTy :: TyCh m => Sigma -> m(Rho)
instanTy s = 
  do { let new nam quant k = do { v <- newFlexiTyVar k; return(TcTv v)}
     ; (env,eqns,r) <- unBindWith new s
     ; unifier <- mguM eqns
     ; return (subRho unifier r) }
    

-- each var according to its Quant, either Rigid or Flexi
--instanPatConstr :: TyCh a => String -> Sigma -> a ([TcTv],[Eqn],Rho)
instanPatConstr q loc s ty = unBindWith new ty
   where new nam Ex k = do { v <- newRigidTyVar q loc s k; return(TcTv v) }
         new nam All k = do { v <- newFlexiTyVar k; return(TcTv v) }

unBindWith :: TyCh m => (Name -> Quant -> Kind -> m Tau) -> Sigma -> m ([TcTv],[Eqn],Rho)
unBindWith new (Forall b) = f b []
 where unTcTv (name,TcTv (v@(Tv _ (Rigid _ _ _) _))) xs = (v:xs)
       unTcTv (name,TcTv (v@(Tv _ (Flexi _) _))) xs = xs
       unTcTv (name,TcTv (v@(Tv _ (Skol _) _))) xs = v:xs
       f (Nil (zs,r)) env = 
          do { r' <- subst env r
             ; zs2 <- subst env zs
             ; return(foldr unTcTv [] env,zs2,r')}
       f (Cons (k,quant) b) env =
          do { (n,xs) <- unbind b
             ; k2 <- subst env k
             ; var <- new n quant k2
             ; f xs ((n,var):env) }

----------------------------------------------------------------------------
-- The opposite of instantiation (Sigma -> Rho) is quantification
-- (Rho -> Sigma). But in general many other things can be quantified other
-- than Rho. Quantification abstracts over each free TcTv as All Quant
-- variables. Ex Quant vars in Forall's come only from Existential types
-- in data defs. Eg.     data Dyn = exists t . Dyn (Rep t) t
-- so quantify  will never produce one.

quantify :: (TypeLike m t,Display t) => [TcTv] -> t -> m Sigma
quantify tvs ty =
  do { (newbinders,ty2) <- subFreshNames tvs [] ty
     ; for_all newbinders ty2
     }



subFreshNames :: (TyCh m,TypeLike m t,Display t)
  => [TcTv] -> [(TcTv,Tau)] -> t -> m([(Name,Kind,Quant)],t)
subFreshNames [] env ty = do { w <- sub ([],env,[]) ty; return([],w) }
subFreshNames (v@(Tv unq (Flexi ref) k):xs) env ty =
   do { name <- fresh
      ; k2 <- sub ([],env,[]) k
      ; (ys,w) <- subFreshNames xs ((v,TyVar name k2):env) ty
      ; return((name,k2,All):ys,w)
      }
subFreshNames (v:xs) env ty = subFreshNames xs env ty -- ignore non-flexi vars      
subFreshNames (v:xs) env ty = 
   failP 0 disp ("\nWhile quantifying over "++t1++"\nwe encountered the non flexi var: "++v1)
      where (disp,t1,v1) = disp2 initDI (ty,v)
      

generalize :: (TypeLike m t,Display t) => t -> m Sigma
generalize rho =
  do { triples <- envTvs
     ; let evars =  varsFromTriples triples
     ; rvars <- get_tvs rho
     --; outputString ("The rho vars are: "++show rvars)
     ; let generic = filter (not . (`elem` evars)) rvars
     ; rho2 <- nf rho
     ; sig <- quantify generic rho2
     ; zonk sig
     }

varsFromTriples triples = foldr acc [] triples
  where acc (name,sigma,vs) vss = vs ++ vss


-------------------------------------------------------------
-- Typable instances

---------------------------------------------------------------------
-- Tell how if a term is Typable as a Rho,
-- one can derive Typabilty as a Sigma for Free!

polyP (Forall (Cons _ _)) = True
polyP (Forall (Nil _)) = False

instance (Show term,Typable m term Rho) => Typable m term Sigma where
  check expr exp_ty
    = do { (skol_tvs, assump, rho) <- skolTy exp_ty
         ; info <- getDisplay
         ; let (info2,orig,skol) = disp2 info (exp_ty,rho)
         ; --when (polyP exp_ty)
                --(outputString ("\nThe type is "++orig++
                --               "\n  skolem is "++skol++
                --               "\n assump = "++show assump++
                --               "\n the term is "++show expr))
         ; s <- (check expr rho)
         --; when (not(null need))
         --       (escapes2 need)
         ; trips <- envTvs
         ; let env_tvs = varsFromTriples trips
         ; tvs2    <- get_tvs exp_ty
         ; let esc_tvs = env_tvs ++ tvs2
               bad_tvs = filter (`elem` esc_tvs) skol_tvs
         ; case bad_tvs of
              [] -> return ()
              zs -> failP 1 info2 ("Type not polymorphic enough" ++ show zs)
         ; return s }

  -- We're defining, infer :: Typable a Sigma => a -> Tc Sigma
  -- inside we use,  infer :: Typable a Rho => a -> Tc Rho
  infer e           
   = do { (exp_ty::Rho,s) <- infer e
        ; res_tvs <- get_tvs exp_ty
        ; trips <- envTvs
        ; let env_tvs = varsFromTriples trips   -- Guaranteed zonked
        ; let forall_tvs = res_tvs \\ env_tvs
        ; t <- quantify forall_tvs exp_ty
        ; return(t,s) }

------------------------------------------------------
-- How to do Kind inference for all 3 forms of types.
-- Tau :: Tau , Rho :: Tau , and Sigma :: Tau
------------------------------------------------------

getTy (Check s) = return s
getTy (Infer ref) = readRef ref
   
-- first show that each can be infered to have a Tau type.
instance TyCh m => Typable m Tau Tau where
  tc tau expect = do { r <- prune tau
                     ; w <- zonk r
                     --; outputString ("Checking "++show tau++" :: "++show expect)
                     ; ans <- f r expect
                     --; k <- getTy expect
                     --; outputString ("Returning "++show tau++" :: "++show k)
                     ; return ans
                     } where                
    f t@(TcTv (Tv u r (MK rho))) expect = mustBe ("type","kind") t rho expect
    f t@(TyCon s k) expect = zapPoly t k expect
    f t@(Star n) expect = mustBe ("kind","sort") t (Star (n+1)) expect
    f (Karr x y) expect = 
      do { (k :: Tau,x1) <- infer x
         ; y1 <- tc y expect
         ; return(Karr x1 y1) }
    f t@(TyVar n (MK k)) expect = zap t k expect 
    f t@(TyFun nm k xs) expect = 
      do { ys <- checkTyFun nm (unpoly k) xs expect; return(TyFun nm k ys)}
    f t@(TyApp ff x) expect =
      do { (fk,a) <- infer ff
         ; fk2 <- zonk fk
         ; (arg_ty,res_ty) <- unifyKindFun ff fk2
         ; let err disp mess = failP 2 disp2
                 ("\nwhile checking the kind of "++show dt++" we expected "++show dx
                  ++" to have kind "++show darg++" because "++show df++
                  " has kind "++show dfk2++
                  " but "++mess)
                  where (disp2,dt,dx,darg,df,dfk2) = disp5 disp (t,x,arg_ty,ff,fk2)
         ; b <- handleM 2 (check x arg_ty) err
         ; morepoly res_ty expect
         ; return (TyApp a b)}

checkTyFun :: TyCh m => String -> Kind -> [Tau] -> Expected Tau -> m [Tau]
checkTyFun nm (MK k) [] (Infer ref) = do { writeRef ref k; return[] }
checkTyFun nm (MK k) [] (Check m) = do { morepoly k m; return [] }
checkTyFun nm (MK k) (t:ts) expect = 
  do { (dom,rng) <- unifyKindFun t k
     ; t2 <- check t dom
     ; ts2 <- checkTyFun nm (MK rng) ts expect
     ; return(t2:ts2)
     }



------------------------------------------------------------
-- Helper functions for kind inference
           
unifyKindFun :: TyCh m => Tau -> Tau -> m (Tau,Tau)
unifyKindFun term (Karr x y) = return (x,y)
unifyKindFun term x@(TcTv (Tv unq _ k)) = 
   do { a <- newTau k
      ; b <- newTau k
      ; unify x (Karr a b)
      ; a1 <- zonk a
      ; b1 <- zonk b
      --; outputString "IN UNifyKindFun"
      ; return (a1,b1) }
unifyKindFun term x = failP 1 disp
         ("\nWhile infering the kind of the type\n   "++ dterm ++
          "\nWe expected a kind arrow (_ ~> _),\n but inferred: "++
          dx++" instead")
   where (disp,dterm,dx) = disp2 initDI (term,x)

zap :: Subsumption m b b => c -> b -> Expected b -> m c
zap term rho (Check r) = do { morepoly rho r; return term }
zap term rho (Infer r) = writeRef r rho >> return term

zapPoly :: TyCh m => Tau -> PolyKind -> Expected Tau -> m Tau
zapPoly (term@(TyCon s k)) (K sig) expect = 
    do { rho <- instanTy sig
       ; sig2 <- zonk sig
       ; rho2 <- instanTy sig2           
       ; case rho of
            Rtau w -> mustBe ("Constructor","type") term w expect
            rho -> fail ("An unexpected Rho appeared while kind checking "++
                         show term ++ " :: "++show rho)
       }


zonkT :: TyCh m => Tau -> m Tau
zonkT = zonk

-- mustBe is a specialized version of zap, with better error reporting
mustBe :: TyCh m => (String,String) -> Tau -> Tau -> Expected Tau -> m Tau
mustBe (term,qual) t comput expect = handleM 1 (zap t comput expect) (errZap expect)
  where errZap :: TyCh m => (Expected Tau) -> DispInfo -> String -> m a
        errZap (Check r) dispIn message =
         do { tz <- zonk t
            ; rz <- zonk r
            ; computz <- zonk comput
            ; let (disp,dtz,dcomputz,drz) = disp3 dispIn (tz,computz,rz)
            ; failP 1 disp ("\nWe computed the "++term++" "++dtz++
                            " to have "++qual++" "++dcomputz++
                  "\nWe expected it to be "++drz++"\n"++message)
            }

         
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
  tc sigma expect = 
     do { let new nam quant k = do { v <- newFlexiTyVar k; return(TcTv v)}
        ; (env,eqs,b) <- unBindWith new sigma
        ; b2 <- tc b expect
        ; eqs2 <- mapM sameEqPair eqs
        ; return(sigma)}  -- WE DON't RETURN THE REBUILT TERM HERE,
                          -- DOES THIS MATTER?

 


hasKind :: TyCh m => String -> Sigma -> Kind -> m ()
hasKind name sigma (MK kind) =
  do { let new nam quant k = do { v <- newFlexiTyVar k; return(TcTv v)}
     ; (env,eqs,rho) <- unBindWith new sigma
     ; let err disp1 message = failP 3 dsp3 string
            where string = ("\nWhile checking the kind of constructor\n   "++
                           name++" :: "++(constr eqs)++dtyp++message++"\n"++show dsp3)
                  (dsp3,dtyp,deqs) = disp2 disp1 (rho,eqs)  
                  constr [] = ""
                  constr (_:_) = deqs
           err2 disp mess = err disp ("$$$ While checking Constraints "++mess)
                  
     ; handleM 3 (check rho kind) err
     ; handleM 3 (mapM sameEqPair eqs) err2
     ; return ()
     }

 

sameEqPair :: TyCh m => Eqn -> m Eqn
sameEqPair(Equality a b) = 
  handleM 1 (do{(k1::Tau,t1) <- infer a; t2 <- check b k1; return(Equality t1 t2)})
    (\ dis s -> fail ("While checking equality constraint: "++
                  show a ++" = "++ show b++"\nkinds do not match"++s))


-----------------------------------------------------
-- A helper function for reporting errors when "morepoly" fails.

escapes2 [] = return ()
escapes2 bad = failP 0 initDI (concat (map f bad))
  where f (v@(Tv _ (Rigid All loc s) k),t) =
           "The explict typing: "++s++
           "\nAt "++show loc++" is too polymorphic."++
           "\nThe variable "++show v++" must be instantiated to "++show t
        f (Tv _ (Rigid Ex loc s) k,t) =
           "An existential type var, arising from the pattern: "++ s ++
           " at "++show loc++ " cannot be equal to "++show t


captured sig1 sig2 rho dispInfo mess =
  failP 0 dispInfo (show sig1++" is not more polymorphic than\n"++show sig2 ++"\n"++
        "Because the skolemized version of the second type: "++show rho++
        "\nhas the following problem: "++mess)


----------------------------------------------------------------
-- Subsumption instances

instance TyCh m => Subsumption m Tau Tau where
   morepoly x y = unify x y

instance Subsumption m b b => Subsumption m b (Expected b) where
   morepoly t1 (Check t2) = morepoly t1 t2
   morepoly t1 (Infer r)  = writeRef r t1

instance TyCh m => Subsumption m PolyKind PolyKind where
  morepoly (K x) (K y) = morepoly x y

instance TyCh m => Subsumption m Sigma Sigma where
  morepoly sigma1 sigma2 =
     do { (skol_tvs,assump,rho) <- skolTy sigma2
        ; unifier <- return []  -- mguM assump
        ; (_,residual::[Eqn]) <- 
             extractAccum (handleM 1 (assume unifier (morepoly sigma1 rho))
                                     (captured sigma1 sigma2 rho))
        ; tv1 <- get_tvs sigma1
        ; tv2 <- get_tvs sigma2
        ; tv3 <- get_tvs residual
        ; let esc_tvs = tv1++tv2++tv3
              bad_tvs = filter (`elem` esc_tvs) skol_tvs
        ; case bad_tvs of
            [] -> injectAccum residual
            zs -> failP 0 initDI ("Not more poly"++show zs)
        }

instance TyCh m => Subsumption m Sigma (Expected Rho) where
   morepoly s1 (Check e2) = morepoly s1 e2
   morepoly s1 (Infer ref) =
      do { rho1 <- instanTy s1;
         ; writeRef ref rho1
         --; assumptions <- getAssume
         --; outputString "In morepoly Sigma (Expected Rho)"
         --; handleM 1 (solve2 oblig1) -- (solve False "morePoly Sigma Rho Infer" assumptions oblig1)
         --    (no_solution s1 rho1 rho1)
         }

norm (Equality x y) = 
  do { -- outputString ("Normalizing "++show x++" and "++show y++"\n");
       a <- normform x
     ; b <- normform y
     ; ((),oblig2) <- extract(unify a b)
     ; return oblig2}

solve2 :: TyCh m => [Eqn] -> m ()
solve2 [] = return ()
solve2 eqns = 
  do { eqns2 <- zonk eqns      
     ; eqns3 <- mapM norm eqns2
     ; let eqns4 = concat eqns3
     ; let residual = filter (\(Equality x y) -> not(x==y)) eqns4
     --; outputString ("eqn = "++show eqns2++"\neqns3 = "++show eqns4)
     ; case residual of
         [] -> return ()
         zs -> let (d1,obl,r1) = disp2 initDI (eqns2,zs)
               in failP 0 d1 ("While trying to solve "++obl++
                              " we get the residual "++r1++gg zs)
     }

gg xs = plistf f " " xs "," "\n"
  where f (Equality x y) = "("++sht x++" , "++sht y++")"
         
instance TyCh m => Subsumption m Sigma Rho where
  morepoly sigma1 rho2 =
     do { --outputString ("\nIn morepoly Sigma Rho\nSigma = "++show sigma1++"\nRho = "++show rho2);
          rho1 <- instanTy sigma1
        --; outputString ("rho1 = "++show rho1++" rho2 = "++show rr)
        ; ((),oblig2) <- extract(morepoly rho1 rho2)
        ; handleM 1 (solve2 (oblig2))  
                    (no_solution sigma1 rho2 rho1)
        }

no_solution sigma rho skoRho info s = failP 1 info2 message
  where (info2,ss,rs,skrs) = disp3 info (sigma,rho,skoRho)
        message = "while checking that\n   "++ss++
                   "\nwas more polymorphic than\n   "++rs++
                   "\nwe skolemized the second to get\n   "++skrs++
                   "\nbut, "++s

instance TyCh m => Subsumption m Rho Rho where
 morepoly x y = f x y where
  f (Rarrow a b) x = do{(m,n) <- unifyFun x; morepoly b n; morepoly m a }
  f x (Rarrow m n) = do{(a,b) <- unifyFun x; morepoly b n; morepoly m a }
  f (Rpair m n) (Rpair a b) = do{ morepoly m a; morepoly n b }
  f (Rpair m n) x = do{(a,b) <- checkPair x; morepoly m a; morepoly n b}
  f x (Rpair a b) = do{(m,n) <- checkPair x; morepoly m a; morepoly n b}
  f (Rsum m n) (Rsum a b) = do{ morepoly m a; morepoly n b }
  f (Rsum m n) x = do{(a,b) <- checkSum x; morepoly m a; morepoly n b}
  f x (Rsum a b) = do{(m,n) <- checkSum x; morepoly m a; morepoly n b}
  f (Rtau x) (Rtau y) = 
     do { --outputString ("Enter unify "++show x++" =? "++show y)
        ; w <- unify x y
        --; outputString "Exit unify"
        ; return w
        }
  f x y = fail ("Bad subsumption. "++show x++
                " is not more polymorphic than "++show y)


checkPair :: TyCh m => Rho -> m (Sigma,Sigma)
checkPair (Rtau x) =
   do { a <- newTau star
      ; b <- newTau star
      ; unify x (tpair a b)
      ; return (simpleSigma a,simpleSigma b) }
checkPair x = fail ("Expecting a pair type: "++show x)

checkSum :: TyCh m => Rho -> m (Sigma,Sigma)
checkSum (Rtau x) =
   do { a <- newTau star
      ; b <- newTau star
      ; unify x (tsum a b)
      ; return (simpleSigma a,simpleSigma b) }
checkSum x = fail ("Expecting a sum type: "++show x)

{- ===================================================
---------------------------------------------------------------------------
--- Solving Equational Constraints

-- The skCount of a term is the number of distinct skolem variables
skCount :: TyCh m => Tau -> m Int
skCount tau = do { vs <- get_tvs tau; return(length(filter isSkol vs))}
  where isSkol (Tv uniq (Skol _) k) = True
        isSkol _ = False

-- The unique representative of an equivalence class 
-- [(s1=ta),(s1=tb),(s1=tc)] is (s1,ti) where ti has the lowest skCount. 
-- If ta and tb tie, with the same count, then choose one arbitrarily.

equivClassRep :: TyCh m => [(TcTv,Tau)] -> m ((TcTv,Tau),[(Int,TcTv,Tau)])
equivClassRep xs = do { ys <-  mapM f xs; return(head (sortBy less ys)) }
  where f (x,t) = do { n <- skCount t; return (n,x,t) }
        less (n,_,_) (m,_,_) = compare n m
        head ((count,var,term):xs) = ((var,term),xs)

-- To simplify an equivalence class, choose a rep (var,typ) and unify 
-- all the types of the other members of the class with "typ". Return 
-- the representative pair, and all the additional Eqn's generated by 
-- the unification.

simpEquivClass :: TyCh m => [(TcTv,Tau)] -> m ((TcTv,Tau),[(TcTv,Tau)])
simpEquivClass [x] = return (x,[])
simpEquivClass xs =
  do { ((skolVar,tau),others) <- equivClassRep xs
     ; (_,oblig) <- extractAccum(mapM (\(cnt,v,t) -> unify tau t) others)
     ; t2 <- zonk tau
     ; return((skolVar,t2),map fixEqn oblig) }

-- To simplify a list of equivalence classes, repeatedly simplify each
-- class until a pass is obtained that never adds any additional new 
-- Eqn's. When that happens return the list of representative pairs, 
-- which is itself an [Eqn]

simpClasses :: TyCh m => [[(TcTv,Tau)]] -> m [(TcTv,Tau)]
simpClasses classes =  
   do { ans <- mapM simpEquivClass classes
      ; if finished ans then return(map fst ans) else step ans}
  where finished xs = all (\ (x,new) -> null new) xs
        step xs = simpClasses(mkEquivClass new)
           where new = foldr acc [] xs
                 acc (x,new) more = x : (new ++ more)

mkEquivClass :: [(TcTv,Tau)] -> [[(TcTv,Tau)]]
mkEquivClass zs = (groupBy eq (sortBy less zs))
  where eq (x,t1) (y,t2) = x==y
        less (x,t1) (y,t2) = compare x y

-- The Eqn extracted from accumulating unification should have a special
-- form. The LHS of the equation should always be a TcTv Skol var.
fixEqn (TcTv v,tau) = (v,tau)
fixEqn (tau,TcTv v) = (v,tau)
fixEqn (x,tau) = error ("Non Var as lhs of Eqn after unify: "++show x++" = "++show tau)


solve :: TyCh m => Bool -> String -> [Eqn] -> [Eqn] -> m ()
solve verbose s assumptions [] = return ()
solve verbose s assumptions obligations =
  do { a1 <- zonk assumptions; o1 <- zonk obligations
     ; when (verbose && consp assumptions && consp obligations) $
            outputString ("\nSolve: "++s++showEqn a1++" ==> "++showEqn o1)
     --; outputString "\nTurning EQN into Theta in Solve\n"
     ; (_,true_pairs::[Eqn]) <- 
             handleM 1
             (extractAccum(mapM (uncurry unify) a1)) 
             (unsat a1)
     ; (_,test_pairs::[Eqn]) <- extractAccum(mapM (uncurry unify) o1)
     --; outputString ("Test pairs = "++showEqn test_pairs++show o1)
     --; outputString ("True pairs = "++showEqn true_pairs)
     ; truths <- simpClasses(mkEquivClass(map fixEqn true_pairs))
     ; residual <- checkEach (matches 5) truths (map fixEqn test_pairs)
     ; let f (x,y) = (TcTv x,y)
     ; injectAccum ((map f residual)::[Eqn])
     }

unsat :: TyCh m => [Eqn] -> DispInfo -> String -> m a
unsat assump dispIn s = 
  do { let (dispOut,truths) = disp dispIn assump
     ; failP 0 dispOut ("The assumptions "++truths++
                        "\nare unsatisfiable, because "++s)
     }

consp (x:xs) = True
consp [] = False

------------------------------------------------------
-- lookupEquality (v,t) {(v1,t1),(v2,t2),(v3,v4)} =
-- case (v,t) of
--   (v1,X)  -> Just (v1,X,t1)
--   (v1,v4) -> Just (v3,v4,v1) -- we might find LHS in the list of truths
--
-- if it returns (x,y,z) we know x is bound in the truths,
--                               and y and z should be unified

lookUpEquality (v,t1) truths =
  case lookup v truths of
    Nothing ->
      case t1 of
        TcTv u ->
          case lookup u truths of
            Nothing -> Nothing
            Just t2 -> Just(u,TcTv v,t2)
        other -> Nothing
    Just t2 -> Just(v,t1,t2)

--checkEach :: TyCh m => [(TcTv,Tau)] -> [(TcTv,Tau)] -> m [(TcTv,Tau)]
checkEach matchFun truths [] = return []
checkEach matchFun truths ((v,t1):more) =
  case lookUpEquality (v,t1) truths of
    Just(v,t1,t2) -> do { xs <- matchFun truths t1 t2
                        ; ys <- checkEach matchFun truths more
                        ; return(xs ++ys) }
    Nothing -> (checkFail 2 truths v t1)

checkFail n truths v t =
  do { info <- getDisplay
     ; let (info2,eqns,vs,ts) = disp3 info (truths,v,t)
     ; failP 0 info2 ("\n"++show n ++ " Under "++eqns++"\nThe equation: "++vs++" = "++ts++ " cannot be solved\n")
     }
     
matches :: TyCh m => Int -> [(TcTv,Tau)] -> Tau -> Tau -> m [(TcTv,Tau)]
matches 0 truths (TcTv v) (TcTv u) | v==u = return []
matches 0 truths v t = (checkFail 1 truths v t)
matches n truths x y =
  do {(_,extra::[Eqn]) <- extractAccum(unify x y)
     ; checkEach (matches (n-1)) truths (map fixEqn extra)   
     }
     


======================================================== -}

showEqn xs = plistf g "{" xs ", " "}"
  where g (Equality x y) = show x ++ " = " ++ show y
  

showPairs xs = plistf g "{" xs ", " "}"
  where g (x,y) = show x ++ " = " ++ show y
  
extract :: TyCh m => m a -> m (a,[Eqn])
extract comp = do { (a,eqs) <- extractAccum comp
                   ; eqs2 <- zonk eqs; return(a,eqs2) }

--------------------------------------------------------------------------
--------------------------------------------------------------------------
-- Parsing types. Note that we parse type PT, and then translate

data PT
  = TyVar' String
  | Rarrow' PT PT
  | Karrow' PT PT
  | TyApp' PT PT
  | TyFun' [PT]
  | TyCon' String
  | Star' Int
  | Forallx [(String,PT,Quant)] [(PT,PT)] PT
  | Tlamx String PT
  | AnyTyp Int -- Gen up a new var with kind (Star Int)

samePT (TyVar' x) (TyVar' y) = x==y
samePT (Rarrow' x y) (Rarrow' m n) = samePT x m && samePT y n
samePT (Karrow' x y) (Karrow' m n) = samePT x m && samePT y n
samePT (TyApp' x y) (TyApp' m n) = samePT x m && samePT y n
samePT (TyCon' x) (TyCon' y) = x==y
samePT (Star' x) (Star' y) = x==y
samePT _ _ = False

getFree :: [String] -> PT -> [String]
getFree bnd (TyVar' s) = if elem s bnd then [] else [s]
getFree bnd (Rarrow' x y) = union (getFree bnd x) (getFree bnd y)
getFree bnd (Karrow' x y) = union (getFree bnd x) (getFree bnd y)
getFree bnd (TyFun' x) = foldr g [] x 
    where g t free = union (getFree bnd t) free
getFree bnd (TyApp' x y) = (getFree bnd x) `union` (getFree bnd y)
getFree bnd (TyCon' s) = []
getFree bnd (Star' n) = []
getFree bnd (Tlamx n t) = getFree (n:bnd) t
getFree bnd (AnyTyp n) = []
getFree bnd (Forallx xs eqs t) = f bnd xs t `union` g bnd eqs
  where f bnd [] t = getFree bnd t
        f bnd ((s,a,q):xs) t = (getFree bnd a) `union` (f (s:bnd) xs t)
        g bnd [] = []
        g bnd ((a,b):xs) = (getFree bnd a) `union` (getFree bnd b) `union` g bnd xs


-- Get all the variables appearing in the type, both free and bound
getAll :: PT -> [String]
getAll (TyVar' s) = [s]
getAll (Rarrow' x y) = union (getAll x) (getAll y)
getAll (Karrow' x y) = union (getAll x) (getAll y)
getAll (TyFun' x) = foldr g [] x 
    where g t free = union (getAll t) free
getAll (TyApp' x y) = (getAll x) `union` (getAll y)
getAll (TyCon' s) = []
getAll (Star' n) = []
getAll (Tlamx n t) = getAll t
getAll (AnyTyp n) = []
getAll (Forallx xs eqs t) = f xs t `union` g eqs
  where f [] t = getAll t
        f ((s,a,q):xs) t = (getAll a) `union` (f xs t)
        g [] = []
        g ((a,b):xs) = (getAll a) `union` (getAll b) `union` g xs


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
  (TyCon' s) -> return(TyCon' s)
  (Star' n) -> return(Star' n)
  (AnyTyp n) -> return(AnyTyp n)
  (Tlamx n t) ->
    do { m <- fresh n
       ; s <- subPT ((n,m):sigma) fresh t
       ; return(Tlamx m s)}
  (Forallx xs eqs t) -> 
    do { let fresh1 (x,y,z) = do { x1 <- fresh x; return(x,x1)}
             g (x,y,z) (_,x1) = (x1,y,z)
       ; xs1 <- mapM fresh1 xs
       ; let sigma1 = xs1 ++ sigma
             rcall1 x = subPT sigma1 fresh x
             f (x,y) = do { a <- rcall1 x; b <- rcall1 y; return(a,b)}
       ; eqs1 <- mapM f eqs
       ; t1 <- rcall1 t
       ; return(Forallx (zipWith g xs xs1) eqs1 t1)}

-- Apply a substitution, but don't rename any of the binding
-- occurences. The user must be sure that this doesn't matter.
ptsub :: [(String,String)] -> PT -> PT
ptsub sigma x = 
 let rcall x = ptsub sigma x
 in case x of 
  (TyVar' s) -> case lookup s sigma of {Just t -> TyVar' t; Nothing -> TyVar' s}
  (Rarrow' x y) -> Rarrow' (rcall x) (rcall y)
  (Karrow' x y) -> Karrow' (rcall x) (rcall y) 
  (TyFun' xs)   -> TyFun'(map rcall xs)
  (TyApp' x y)  -> TyApp' (rcall x) (rcall y)
  (TyCon' s) -> (TyCon' s)
  (Star' n) -> (Star' n)
  (AnyTyp n) -> (AnyTyp n)
  (Tlamx n t) -> Tlamx n (ptsub ((n,n):sigma) t) 
  (Forallx xs eqs t) -> 
   let sub1 (nm,kind,quant) = (nm,ptsub sigma kind,quant)
       sub2 (t1,t2) = (rcall t1,rcall t2)
    in Forallx (map sub1 xs) (map sub2 eqs) (rcall t)

   
--------------------------------------------------------------------
-- Translating. The translation respects (and enforces) the 3 level
-- distinctions between Sigma, Rho and Tau.
 
toSigma :: TyCh m => ToEnv -> PT -> m Sigma
toSigma env (Forallx xs eqs body) =
   do { (fargs,env2) <- argsToEnv xs env
      ; r <- toRho env2 body
      ; eqs2 <- toEqs env2 eqs
      ; return(Forall (windup fargs (eqs2,r))) }
toSigma env x = do { r <- toRho env x; return(Forall (Nil ([],r)))}

toEqs :: TyCh m => ToEnv -> [(PT,PT)] -> m [Eqn]
toEqs env [] = return []
toEqs env ((a,b):xs) =
  do { m <- toTau env a
     ; n <- toTau env b
     ; ys <- toEqs env xs
     ; return((Equality m n):ys) }

toRho env (Rarrow' x y) =
  do { s <- toSigma env x; r <- toRho env y; return(arrow s r)}
toRho env (TyApp' (TyApp' (TyCon' "(,)") x) y) =
  do { a <- toSigma env x; b <- toSigma env y; return(pair a b)}
toRho env (TyApp' (TyApp' (TyCon' "(+)") x) y) =
  do { a <- toSigma env x; b <- toSigma env y; return(rsum a b)}
toRho env t = do { w <- toTau env t; return(Rtau w) }


toTau :: TyCh m => ToEnv -> PT -> m Tau
toTau env (TyVar' s) = readName "In To Tau (TyVar' _): " env s
toTau env (Rarrow' x y) =
  do { s <- toTau env x; r <- toTau env y; return(tarr s r)}
toTau env (Karrow' x y) =
  do { s <- toTau env x; r <- toTau env y; return(Karr s r)}  
toTau env (ty@(TyFun' (x:xs))) =   
  do { s <- toTau env x
     ; ys <- mapM (toTau env) xs
     ; case s of
        TyCon nm k -> return(TyFun nm k ys)
        _ -> fail ("\n"++ show ty++" doesn't have type var in function position"++sht s++show x)
     }
toTau env (TyApp' x y) = 
  do { z <- toTau env x; r <- toTau env y; return(TyApp z r)}
toTau env (TyCon' s) = readName "In To Tau (TyCon' _): " env s
toTau env (Star' n) = return(Star n)
toTau env (t@(Forallx xs eqs body)) = 
  fail ("Sigma type in Tau context: "++show t)
toTau env (t@(Tlamx s x)) = fail ("No lambda types in rankN: "++show t)
toTau env (AnyTyp n) = 
   do { k <- newKind (MK(Star n))
      ; v <- newFlexiTyVar (MK (Star n)) ; return(TcTv v)}


argsToEnv :: TyCh m => [(String,PT,Quant)] -> ToEnv -> m (ForAllArgs,ToEnv)
argsToEnv [] env = return([],env)
argsToEnv ((s,k,quant):xs) env =
 do { w <- toTau env k
    ; let k2 = MK w
    ; nm <- fresh
    ; (zs,env2) <- argsToEnv xs ((s,TyVar nm k2,poly k2):env)
    ; return ((nm,k2,quant):zs,env2)
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

simpletyp :: Int -> Parser PT
simpletyp strata =
       do {t <- constructorName; return (TyCon' t) }          -- T
   <|> do {x <- identifier; return (TyVar' x) }               -- x
   <|> (symbol "?" >> return (AnyTyp (strata + 1)))           -- ?
   <|> parseStar                                              -- * *1 *2

   -- () and []
   <|> try (do { x <- (symbol "()" <|> symbol "[]"); return(TyCon' x)})  
   -- (->) (+) and (,)   
   <|> try (do { x <- parens(symbol "->" <|> symbol "+" <|> symbol ",")  
               ; return(TyCon' ("("++x++")"))})

   <|> try (parens(do { x <- identifier; symbol "."
                      ; t <- typN strata; return(Tlamx x t)})) -- (x.[x])
   <|> try(do {ts <- parens(sepBy1 (typN strata) (symbol ",")) -- (t,t,t)
              ; return (tprods' ts)})
   <|> try(do {ts <- parens(sepBy1 (typN strata) (symbol "+")) -- (t+t+t)
              ; return (tsums' ts)})
   <|> do {t <- squares (typN strata); return (list' t)}       -- [t]
   <|> (do { xs <- braces (many1 (simpletyp strata)); return(TyFun' xs)}) -- {plus x y}

constructorName = lexeme (try construct)
  where construct = do{ c <- upper
                      ; cs <- many (identLetter tokenDef)
                      ; return (c:cs) }
                    <?> "Constructor name"

parseStar = lexeme(do{char '*'; ds <- many digit; return(Star' (val ds))})
  where val :: String -> Int
        val [] = 0
        val xs = read xs

arrTyp n =
   do { ts <- many1 (simpletyp n)-- "f x y -> z"  parses as "(f x y) -> z"
      ; let d = (applyT' ts)     -- since (f x y) binds tighter than (->)
      ; range <- possible 
                 ((do {symbol "->"; ans <- typN n; return(True,ans)}) <|>
                  (do {symbol "~>"; ans <- typN n; return(False,ans)}) )
      ; case range of
           Nothing -> return d
           Just(True,r) -> return(Rarrow' d r)
           Just(False,r) -> return(Karrow' d r)
      }

allTyp n =
  do { reserved "forall"
     ; ns <- many1 (argument n All)
     ; symbol "."
     ; eqs <- possible(do { xs <- parens(sepBy (equality n) comma)
                          ; symbol "=>"; return xs})
     ; let f Nothing = []
           f (Just xs) = xs
     ; t <- typN n
     ; return (Forallx ns (f eqs) t)
     }

argument n q = 
  (do { x <- identifier; return(x,AnyTyp (n+1),q)})  <|>
  parens (do { x <- identifier; reservedOp "::"; k <- typN n; return(x,k,q)})

typN :: Int -> Parser PT
typN n = allTyp n <|> arrTyp n

eqnTyp :: Int -> Parser PT
eqnTyp n = 
   --(do { xs <- between (symbol "{") (symbol "}") (arrTyp n); return(TyFun' [xs])}) <|>
   (arrTyp n)



equality n =
 do { t1 <- eqnTyp n 
    ; reservedOp "="
    ; t2 <- eqnTyp n
    ; return(t1,t2)
    }

   
pt s = case parse2 (typN 0) s of { Right(x,more) -> x; Left s -> error (show s) }
peqt s = case parse2 (eqnTyp 0) s of { Right(x,more) -> x; Left s -> error s }

parseSigma :: TyCh m => String -> m Sigma
parseSigma s = toSigma toEnv0 (pt s)

getrho :: TyCh m => [Char] -> m Rho
getrho s = toRho toEnv0 (pt s)


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

instance Show PT where
  show (TyVar' s) = s
  show (Rarrow' x y) = showp x ++ " -> "++show y
  show (Karrow' x y) = showp x ++ " ~> "++show y
  show (TyApp' (TyCon' "[]") x) = "[" ++ show x ++ "]"
  show (TyApp'(TyApp'(TyCon' "(,)") x) y)= "("++show x++","++show y++")"
  show (TyApp'(TyApp'(TyCon' "(+)") x) y)= "("++show x++"+"++show y++")"
  show (TyApp' x (y@(TyApp' _ _))) = show x ++ " " ++ showp y
  show (TyApp' x y) = show x ++ " " ++ showp y
  show (TyCon' s) = s
  show (TyFun' xs) = plist "{" xs " " "}"
  show (Star' n) = "*"++show n
  show (Tlamx n t) = "("++n++" . "++show t++")"
  show (AnyTyp n) = "?::*"++show n
  show (Forallx xs eqs t) = "(forall "++ f xs++ g eqs ++ show t ++ ")"
    where f [(s,AnyTyp _,q)] = s ++ shq q ++ " . "
          f ((s,AnyTyp _,q):xs) = s ++ shq q++ " "++f xs
          f [(s,k,q)] = "("++ s ++ shq q++ "::" ++ show k ++") . "
          f ((s,k,q):xs) = "("++ s++ shq q ++ "::" ++ show k ++") "++f xs
          g [] = ""
          g xs = plist "(" xs "," ") => "
          shq All = ""
          shq Ex  = "'"
          
showp x@(Rarrow' _ _) = "("++show x ++ ")" 
showp x@(Karrow' _ _) = "("++show x ++ ")" 
showp x@(TyApp' _ _) = "("++show x ++ ")" 
showp x@(Forallx _ _ _) = "("++show x ++ ")" 
showp x = show x

--------------------------------------------------------------
-- show instances

showparR x@(Forall (Nil (_,Rarrow _ _))) = "("++show x ++ ")"
showparR x = show x

instance Show Rho where
  show (Rarrow x y) = (showparR x)++" r-> "++(show y)
  show (Rpair x y) = "("++(show x)++";"++(show y)++")"
  show (Rsum x y) = "("++(show x)++" | "++(show y)++")"
  show (Rtau x) = (show x)

instance Show Tau where
  show (TyVar nm k) = show nm -- "("++show nm ++":"++show k++")"
  show (TyApp (TyCon "[]" _) (TyCon "Char" _)) = "String"
  show (TyApp (TyCon "[]" _) x) = "[" ++ show x ++ "]"

  show (TyApp(TyApp(TyCon "(,)" _) x) y)= "("++show x++","++show y++")"
  show (TyApp(TyApp(TyCon "(->)" _) x) y)= showpar x ++ " -> "++ show y
  show (TyApp(TyApp(TyCon "(+)" _) x) y)= "("++show x++"+"++show y++")"
  show (TyApp x y) = show x ++ " " ++ showpar y
  show (TyCon s k) = s -- ++"{"++show k++"}"
  show (Star 0) = "*"
  show (Star n) = "*"++show n
  show (Karr x y) = showpar x ++ " ~> "++ show y 
  show (TyFun nm k xs) = "{"++nm ++ plist " " xs " " "}"
  show (TcTv v) = show v

instance Show TcTv where
  show (Tv unq (Rigid _ _ _) k) = "_"++show unq ++ showMono k
  show (Tv unq (Flexi _) k) = "Z"++show unq ++ showMono k
  show (Tv unq (Skol s) k) = "*"++show unq  ++ showMono k

instance Show Sigma where
  show (Forall (Nil (_,x))) = show x
  show (Forall zs) = "(forall "++g xs++" . "++hww t++")"
    where g [(x,k,q)] = show x ++ sh q ++ showMono k
          g ((x,k,q):zs) = show x ++ sh q ++ showMono k ++ " " ++ g zs
          sh All = ""
          sh Ex = "'"
          hww (zs,t) = eqf zs ++ show t
          eqf [] = ""
	  eqf zs = plistf h "(" zs "," ") => "
          h (Equality x y) = show x++ " = "++ show y
          (xs,t) = unsafeUnwind zs
          
instance Show Eqn where
  show (Equality x y) = "("++show x++" = "++show y++")"

unsafeUnwind :: Swap a => L a -> ([(Name,Kind,Quant)],a)         
unsafeUnwind (Nil t) = ([],t)
unsafeUnwind (Cons (k,q) b) = ((x,k,q):xs,t)
   where (x,rest) = unsafeUnBind b
         (xs,t) = unsafeUnwind rest

showMono (MK (Star 0)) = ""
showMono (MK x) = ":"++show x

showpar z@(TyApp (TyApp (TyCon "(,)" _) x) y) = show z
showpar z@(TyApp (TyApp (TyCon "(+)" _) x) y) = show z
showpar z@(TyApp (TyCon "[]" _) x) = show z
showpar x@(TyApp _ _) = "("++show x ++ ")" 
showpar x@(Karr _ _) = "("++show x ++ ")" 
showpar x = show x

showPolyKind (K (Forall (Nil (_,Rtau (Star 0))))) = "*"
showPolyKind (K z) = show z

instance Show Kind where
  show (MK t) = show t

instance Show PolyKind where
  show = showPolyKind

instance Show a => Show (Expected a) where
  show (Check a) = "(Check "++show a++")"
  show (Infer ref) = "Infer"

---------------------------------------------------
class Alpha t where
  alpha :: [(Name,String)] -> t -> String

instance Alpha PolyKind where
  alpha e (K z) = alpha e z

instance Alpha Rho where
  alpha e (Rarrow x y) = (alphaparR e x)++" r-> "++(alpha e y)
  alpha e (Rpair x y) = "("++(alpha e x)++";"++(alpha e y)++")"
  alpha e (Rsum x y) = "("++(alpha e x)++" | "++(alpha e y)++")"
  alpha e (Rtau x) = (alpha e x)


alphapar e z@(TyApp (TyApp (TyCon "(,)" _) x) y) = alpha e z
alphapar e z@(TyApp (TyApp (TyCon "(+)" _) x) y) = alpha e z
alphapar e z@(TyApp (TyCon "[]" _) x) = alpha e z
alphapar e x@(Karr _ _) = "("++alpha e x ++ ")"
alphapar e x@(TyApp _ _) = "("++alpha e x ++ ")" 
alphapar e x = alpha e x

alphaparR e x@(Forall (Nil (_,Rarrow _ _))) = "("++alpha e x ++ ")"
alphaparR e x = alpha e x

alphaMono var e (MK (Star 0)) = var
alphaMono var e (MK z) = "(" ++ var ++":"++alpha e z++")"


instance Alpha Tau where
  alpha e (TyVar nm k) =
     case lookup nm e of { Just s -> s; Nothing -> show nm }
  alpha e (TyApp (TyCon "[]" _) x) = "[" ++ alpha e x ++ "]"
  
  alpha e (TyApp (TyCon "[]" _) (TyCon "Char" _)) = "String"
  alpha e (TyApp (TyApp (TyCon "(,)" _) x) y) = 
        "(" ++ alpha e x ++ ","++ alpha e y ++")"
  alpha e (TyApp (TyApp (TyCon "(->)" _) x) y) = 
        alphapar e x ++ " -> "++ alpha e y
  alpha e (TyApp (TyApp (TyCon "(+)" _) x) y) = 
        "(" ++ alpha e x ++ "+"++ alpha e y ++")"
  alpha e (TyApp x y) = alpha e x ++ " " ++ alphapar e y
  alpha e (TyCon "(->)" _) = "(->)"   -- Never pull on the kind of (->)
  alpha e (TyCon s k) = s -- ++"{"++show k++"}"
  alpha e (Star 0) = "*"
  alpha e (Star n) = "*"++show n
  alpha e (Karr x y) = alphapar e x ++ " ~> "++ alpha e y 
  alpha e (TyFun f k xs) = "{"++f ++ g xs
    where g [x] = " "++alphapar e x++ "}"
          g (x:xs) = " "++alphapar e x++ g xs
  alpha e (TcTv v) = show v

instance Alpha Kind where
  alpha e (MK t) = alpha e t

instance Alpha Sigma where
  alpha e (Forall (Nil (zs,x))) = alpha e x
  alpha e (Forall zs) = "(forall "++args++" . "++eqf eqs++alpha e2 t++")"
    where (args,e2) = g e xs
          g e [(x,k,q)] = (alphaMono (nm ++ sh q) e k,e2)
             where (nm,e2) = rename x k e
          g e ((x,k,q):zs) = (alphaMono (nm ++sh q) e k ++ " " ++ rest,e3)
             where (nm,e2) = rename x k e
                   (rest,e3) = g e2 zs
          eqf [] = ""
          eqf zs = plistf h "(" zs "," ") => "
          h (Equality x y) = alpha e2 x++ " = "++alpha e2 y
          sh All = ""
          sh Ex = "'"
          (xs,(eqs,t)) = unwind zs
          unwind (Nil (eqs,t)) = ([],(eqs,t))
          unwind (Cons (k,q) b) = ((x,k,q):xs,t)
               where (x,rest) = unsafeUnBind b
                     (xs,t) = unwind rest

pprint x = alpha [] x

rename :: Name -> Kind -> [(Name,String)] -> (String,[(Name,String)])
rename name k xs = (new,(name,new):xs)
   where new = first xs (choices k)
         first old (x:xs) = if find x old then first old xs else x
         find x [] = False
         find x ((_,y):old) = if x==y then True else find x old



-- Select an infinite list of possible choices given a Kind
choices :: Kind -> [String]
choices k = case k of
    (MK (Star 0))                                           -> types
    (MK (Karr (Star 0) (Star 0)))                           -> typeConstrs
    (MK (Star 1))                                           -> kinds
    (MK (Karr _ _))                                         -> higherOrder
    _                                                       -> other
  where types       = makeNames "abcde"   -- *
        typeConstrs = makeNames "ts"      -- (* -1-> *)
        kinds       = makeNames "k"       -- *1
        higherOrder = makeNames "fgh"     -- (k -> k)
        other       = makeNames "uvwxyz"  -- other


monadPt = pt "(forall a . a -> t a) -> (forall a b . (t a) -> (a -> t b) -> t b) -> (forall a . ([Char]) -> t a) -> Monad t"

-------------------------------------------------------------------------
-- is one Tau a subterm of another Tau?

instance Eq Tau where
  (TyVar n _) == (TyVar m _) = n==m
  (TyApp a b) == (TyApp m n) = a==m && b==n
  (TyCon n _) == (TyCon m _) = n==m
  (Star n) == (Star m) = n==m
  (Karr a b) == (Karr m n) = a==m && b==n
  (TyFun f _ as) == (TyFun g _ bs) = f==g && as==bs
  (TcTv x) == (TcTv y) = x==y
  _ == _ = False
  
subTerm old term | old==term = True
subTerm old (TyApp x y) = (subTerm old x) || (subTerm old y)
subTerm old (Karr x y) = (subTerm old x) || (subTerm old y)  
subTerm old (TyFun nm k x) = error "What do we do here?" -- subTerm old x
subTerm old _ = False    

replace new old term | old==term = new
replace new old (TyApp x y) =  TyApp (replace new old x) (replace new old y)
replace new old (Karr x y) = Karr (replace new old x) (replace new old y)    
replace new old (TyVar m (MK k)) = TyVar m (MK (replace new old k))
replace new old (TcTv(Tv unq fl (MK k))) = TcTv(Tv unq fl (MK (replace new old k)))
replace new old (TyFun f k x) = TyFun f k (map (replace new old) x)
replace new old term = term  

---------------------------------------------------------------

dispArr xs (t@(TyApp (TyApp (TyCon "(->)" _) x) y)) = (ys,"("++z++")")
  where (ys,z) = disp xs t
dispArr xs t = disp xs t  

instance Display Tau where
  disp xs (TyCon s k) = (xs,s)
  disp e (TyApp (TyCon "[]" _) x) = (ys,"[" ++ ans ++ "]")
    where (ys,ans) = disp e x
  disp e (TyApp (TyApp (TyCon "(,)" _) x) y) = (zs,"(" ++ a ++ ","++ b++")")
    where (ys,a) = disp e x
          (zs,b) = disp ys y 
  disp e (TyApp (TyApp (TyCon "(->)" _) x) y) = (zs,a ++ " -> "++ b)
    where (ys,a) = dispArr e x
          (zs,b) = disp ys y
  disp e (TyApp (TyApp (TyCon "(+)" _) x) y) = (zs,"(" ++ a ++ "+"++ b ++")")
    where (ys,a) = disppar e x
          (zs,b) = disppar ys y        
  disp xs (TyApp x y) = (zs,a++" "++b)
    where (ys,a) = disp xs x
          (zs,b) = disppar ys y
  disp xs (Star 0) = (xs,"*")
  disp xs (Star n) = (xs,"*"++show n)
  disp xs (TyVar nm k) = useDisplay (name2Int nm) f xs 
    where f s = "'"++s
  disp xs (Karr x y) = (zs,a ++ " ~> "++ b)
    where (ys,a) = disp xs x
          (zs,b) = disp ys y
  disp info (TcTv v) =  disp info v
  disp info (TyFun f k xs) = (d2,"{"++f++" "++body++"}")
    where (d2,body) = dispL disppar info xs " "



----------------------------------------
-- we'd like variables to display as (x:k1:*1)

instance Display TcTv where
  disp info (v@(Tv uniq flav (MK k))) = (d2,nameStr ++ suffix)
    where (d1,nameStr) = dispTv info v
          (d2,suffix) = dispMono d1 (MK k)

dispMono info (MK (Star 0)) = (info,"")
dispMono info (MK x) = (d2,":"++z) 
   where (d2,z) = disp info x

tVarPrefix (Flexi _) n = n
tVarPrefix (Rigid _ _ _) n = "_"++n
tVarPrefix (Skol _) n = "*"++n

dispTv :: DispInfo -> TcTv -> (DispInfo,String) 
dispTv d1 (Tv uniq flav k) = useDisplay uniq (tVarPrefix flav) d1

dispKind :: DispInfo -> Tau -> (DispInfo,[Char])
dispKind d1 (Star 0) = (d1,"")
dispKind d1 (t@(Star n)) = (d1,":"++show t)
dispKind d1 (TyVar nm (MK k)) = (d3,":"++nmStr++kStr)
   where (d2,nmStr) = useDisplay (name2Int nm) f d1 where f s = "'"++s
         (d3,kStr) = dispKind d2 k
dispKind d1 (TcTv (v@(Tv _ _ (MK k)))) = (d3,":"++nmStr++kStr)
   where (d2,nmStr) = dispTv d1 v
         (d3,kStr) = dispKind d2 k 
dispKind d1 (TyCon s k) = (d1,":"++s)         
dispKind d1 x = (d1,"?"++show x++"?")         

---------------------------------------------------------            
dispRarr xs (t@(Forall (Cons _ _))) = (ys,"("++z++")")
  where (ys,z) = disp xs t
dispRarr xs (t@(Forall (Nil (_,Rtau (TyApp (TyApp (TyCon "(->)" _) x) y))))) = (ys,"("++z++")")
  where (ys,z) = disp xs t
dispRarr xs t = disp xs t  
        
instance Display Rho where 
  disp xs (Rtau x) = disp xs x
  disp xs (Rarrow x y) = (zs,a++" -> "++b)
    where (ys,a) = dispRarr xs x
          (zs,b) = disp ys y
  disp xs (Rpair x y) = (zs,"("++a++","++b++")")
    where (ys,a) = disp xs x
          (zs,b) = disp ys y
  disp xs (Rsum x y) = (zs,"("++a++"+"++b++")")
    where (ys,a) = disp xs x
          (zs,b) = disp ys y

  
instance Display Sigma where
  disp d1 (Forall args) = (d4,prefix ++ eqsS ++ rhoS)
    where (trips,(eqs,rho)) = unsafeUnwind args
          (d2,prefix) = f d1 trips 
          (d3,eqsS) = disp d2 eqs
          (d4,rhoS) = disp d3 rho
          f d1 [] = (d1,"")
          f d1 trips = (d2,"forall "++argStr ++ " . ")
            where (d2,argStr) = dispL pp d1 trips " "
          pp d2 (nm,MK k,q) = (d4,name ++ kind)
            where (d3,name) = useDisplay (name2Int nm) prefix d2
                  (d4,kind) = dispKind d3 k
                  prefix s = "'"++s++(case q of {Ex -> "'"; All -> ""})
          


instance Display [(Tau,Tau)] where
  disp xs [] = (xs,"")
  disp xs ys = (zs,"( "++ans++" ) => ")
    where (zs,ans) = dispL disp xs ys ", "

instance Display [Eqn] where
  disp xs [] = (xs,"")
  disp xs ys = (zs,"( "++ans++" ) => ")
    where (zs,ans) = dispL disp xs ys ", "
    
instance Display [(TcTv,Tau)] where
  disp xs [] = (xs,"")
  disp xs ys = (zs,"( "++ans++" ) => ")
    where (zs,ans) = dispL disp xs ys ", "


instance Display (Tau,Tau) where
  disp xs (x,y) = (zs,a++"="++b)
    where (ys,a) = disp xs x
          (zs,b) = disp ys y

instance Display Eqn where
  disp xs (Equality x y) = (zs,a++"="++b)
    where (ys,a) = disp xs x
          (zs,b) = disp ys y
          

instance Display ([Eqn], Rho) where
  disp xs (es,r) = (ys,esx ++ " => " ++ rx)
     where (ys,esx,rx) = disp2 xs (es,r)

instance Display (TcTv,Tau) where
  disp xs (x,y) = (zs,a++"="++b)
    where (ys,a) = disp xs x
          (zs,b) = disp ys y

disppar xs z@(TyApp (TyApp (TyCon "(,)" _) x) y) = disp xs z
disppar xs z@(TyApp (TyApp (TyCon "(+)" _) x) y) = disp xs z
disppar xs x@(Karr _ _) = (ys,"("++ ans ++ ")")
  where (ys,ans) = disp xs x 
disppar xs x@(TyApp _ _) = (ys,"("++ans++ ")")
  where (ys,ans) = disp xs x 
disppar xs x = disp xs x

-----------------------------------------------------------
-- Side-effect Free subsitution. Usually you must zonk
-- before calling this function.

subKind :: [(TcTv,Tau)] -> Kind -> Kind
subKind env (MK x) = MK(subTau env x)

subPoly :: [(TcTv,Tau)] -> PolyKind -> PolyKind
subPoly env (K s) = K(subSigma env s)

subSigma :: [(TcTv,Tau)] -> Sigma -> Sigma
subSigma env (Forall xs) = Forall(subL env xs)

subL :: [(TcTv,Tau)] -> L ([Eqn],Rho) -> L ([Eqn],Rho)
subL env (Nil(eqn,rho)) = Nil(subEqn env eqn,subRho env rho)
subL env (Cons (k,q) x) = Cons (subKind env k,q) (bind nm xs)
  where (nm,more) = unsafeUnBind x
        xs = subL env more

subEqn :: [(TcTv,Tau)] -> [Eqn] -> [Eqn]
subEqn env xs = map f xs where f (Equality x y) = Equality (subTau env x) (subTau env y)

subPairs :: [(TcTv,Tau)] -> [(Tau,Tau)] -> [(Tau,Tau)]
subPairs env xs = map f xs where f (x,y) = (subTau env x,subTau env y)


subRho :: [(TcTv,Tau)] -> Rho -> Rho
subRho env (Rarrow s r) = Rarrow (subSigma env s) (subRho env r)
subRho env (Rpair s r) = Rpair (subSigma env s) (subSigma env r)
subRho env (Rsum s r) = Rsum(subSigma env s) (subSigma env r)
subRho env (Rtau t) = Rtau(subTau env t)

subTau :: [(TcTv,Tau)] -> Tau -> Tau
subTau env (TcTv (x@(Tv unq flav k))) = 
   case lookup x env of 
      Nothing -> TcTv (Tv unq flav (subKind env k))
      Just z -> z
subTau env (TyApp x y) =  TyApp (subTau env x) (subTau env y)
subTau env (TyCon s k) = TyCon s k2 where  k2 = subPoly env k
subTau env (Star n) = Star n
subTau env (Karr x y) =  Karr (subTau env x) (subTau env y)
subTau env (TyFun f k x) = TyFun f (subPoly env k) (map (subTau env) x)
subTau env (TyVar s k) = TyVar s (subKind env k)

---------------------------------------------------
-- Get type variables from a term, should be zonked first

tvsTau (TcTv x) = [x]
tvsTau (TyApp x y) = union (tvsTau x) (tvsTau y)
tvsTau (TyCon s k) = tvsPoly k
tvsTau (Star n) = []
tvsTau (Karr x y) = union (tvsTau x) (tvsTau y)
tvsTau (TyFun f k xs) = union (tvsPoly k) (foldr g [] xs)  where g t vs = union (tvsTau t) vs
tvsTau (TyVar s k) = tvsKind k

tvsPoly(K x) = tvsSigma x

tvsKind (MK x) = tvsTau x

tvsSigma (Forall z) = tvsL z

tvsL (Nil(eqns,rho)) = union (tvsEqn eqns) (tvsRho rho)
tvsL (Cons (k,q) x) = union(tvsKind k) (tvsL more)
  where (nm,more) = unsafeUnBind x
 
tvsEqn [] = []
tvsEqn ((Equality x y):xs) = union (union (tvsTau x) (tvsTau y)) (tvsEqn xs)

tvsRho (Rarrow x y) = union (tvsSigma x) (tvsRho y)
tvsRho (Rpair x y) = union (tvsSigma x) (tvsSigma y)
tvsRho (Rsum x y) = union (tvsSigma x) (tvsSigma y)
tvsRho (Rtau x) = tvsTau x

---------------------------------------------------------------
-- Computing most general unifiers. Done in a side effect free way
-- Note that Flexi vars might be bound in the unifer returned.
-- A computational pass can force these to be unified unified later if
-- necessary. See the function "mutVarSolve" and "mguM"

mgu :: [(Tau,Tau)] -> Either [(TcTv,Tau)] (String,Tau,Tau)
mgu [] = Left []
mgu ((TcTv (Tv n _ _),TcTv (Tv m _ _)):xs) | n==m = mgu xs
mgu ((TcTv (x@(Tv n (Rigid _ _ _) _)),tau):xs) = mguVar x tau xs
mgu ((tau,TcTv (x@(Tv n (Rigid _ _ _) _))):xs) = mguVar x tau xs
mgu ((TcTv (x@(Tv n (Flexi _) _)),tau):xs) = mguVar x tau xs
mgu ((tau,TcTv (x@(Tv n (Flexi _) _))):xs) = mguVar x tau xs
mgu ((TcTv x,TcTv y):xs) | x==y = mgu xs
mgu ((TyApp x y,TyApp a b):xs) = mgu ((x,a):(y,b):xs)
mgu ((TyCon s1 _,TyCon s2 _):xs) | s1==s2 = mgu xs
mgu ((Star n,Star m):xs) | n==m = mgu xs
mgu ((Karr x y,Karr a b):xs) = mgu ((x,a):(y,b):xs)
mgu ((x@(TyFun f _ ys),y@(TyFun g _ zs)):xs) = 
  if f==g then mgu (zip ys zs ++ xs) else Right("TyFun doesn't match",x,y)
mgu ((x@(TyVar s k),y):xs) = Right("No TyVar in MGU", x, y)
mgu ((y,x@(TyVar s k)):xs) = Right("No TyVar in MGU", x, y)
mgu ((x,y):xs) = Right("No Match", x, y)

mguVar x tau xs = if (elem x vs) 
                     then Right("occurs check", TcTv x, tau)
                     else compose new2 (Left new1)
  where vs = tvsTau tau
        new1 = [(x,tau)]
        new2 = mgu (subPairs new1 xs)
 
compose (Left s1) (Left s2) = Left ([(u,subTau s1 t) | (u,t) <- s2] ++ s1)
compose _ (Right x) = Right x
compose (Right y) _ = Right y


mguM :: TyCh m => [Eqn] -> m [(TcTv,Tau)]
mguM eqs = 
  do { let f (Equality x y) = (x,y)
     ; xs2 <- zonk (map f eqs)
     ; case mgu xs2 of
        Left ys -> mutVarSolve ys
        Right(s,x,y) -> 
         let (d1,x1,y1,ts) = disp3 initDI (x,y,xs2)
         in failP 0 d1 ("While computing an mgu for "++ts++"\n"++s++" "++x1++" =/= "++y1++"\n")
     }

mutVarSolve [] = return []
mutVarSolve ((x,TcTv(v@(Tv unq (Flexi _) k))):more) = 
  do { unifyVar {- accumulateMGU -} v (TcTv x)
     ; mutVarSolve more }
mutVarSolve ((v@(Tv unq (Flexi _) k),tau):more) = 
  do { unifyVar {- accumulateMGU -} v tau
     ; mutVarSolve more }     
mutVarSolve (x:xs) = do { ys <- mutVarSolve xs; return(x:ys) }

--------------------------------------------------------------------

x2 = [(v 843,Star 0)
     ,(v 764,Karr (v 843) (v 845))
     ]

v n = TcTv(Tv n (Rigid All Z (show n)) star)
u n = (Tv n (Rigid All Z (show n)) star)


x3 = [(v 2626,f(v 2632,v 2634)),(v 2626,f(v 2642,v 2640))]
 where f (x,y) = tpair x y

test2 :: [(Tau,Tau)]
test2 = 
  [(u 843,Star 0)
  ,(u 855,tarr (v 851) (v 853))
  ,(u 845,Star 0)
  ,(u 857,tarr(TyApp (v 847) (v 851)) (TyApp (v 849) (v 853)))
  ,(u 764,Karr (v 843) (v 845))
  ,(u 766,v 847)
  ,(u 766,v 849)
  ,(u 768,tarr (v 855) (v 857))
  ,(u 764,Karr (Star 0) (Star 0))
  ,(u 766,listT)]
 where v n = TcTv(Tv n (Rigid All Z (show n)) star)
       u n = v n

go = mgu test2

-------------------------------------------------------------
-- sometimes when debugging, you need to see
-- what constructors are being used to make
-- a type, since the "show" printed version
-- is ambiguous. "sht" allows you to do this.

sht (TyVar n k) = "(TyVar "++show n++")"
sht (TyApp x y) = "(TyApp "++sht x++" "++sht y++")"
sht (TyCon x k) = "(Con "++show x++")"
sht (Star n) = "(Star "++show n++")"
sht (Karr x y) = "(Karr "++sht x++" "++sht y++")"
sht (TcTv (Tv n (Flexi _) k))  = "(Flex " ++ show n ++")"
sht (TcTv (Tv n (Skol _) k))  = "(Skol " ++ show n ++")"
sht (TcTv (Tv n (Rigid _ _ _) k))  = "(Rigid " ++ show n ++")"
sht (TyFun nm k xs) = "{TyFun "++nm ++ plistf sht " " xs " " "}"
sht x = show x

----------------------------------------------------------
-- Putting types in normal form

nfRho :: TyCh m => Rho -> m Rho
nfRho (Rpair x y) = binaryLift Rpair (nfSigma x) (nfSigma y)
nfRho (Rarrow x y) = binaryLift Rarrow (nfSigma x) (nfRho y)
nfRho (Rsum x y) = binaryLift Rsum (nfSigma x) (nfSigma y)
nfRho (Rtau x) =  do { a <- nfTau x; return(Rtau a) }

nfSigma ::  TyCh m => Sigma -> m Sigma
nfSigma (Forall xs) = 
  do { let (ys,(eqn,rho)) = unsafeUnwind xs
           f (nm,MK k,q) = do { a <- (nfTau k); return (nm,MK a,q)}
     ; eqn2 <- nfEqns eqn
     ; ys2 <- mapM f ys
     ; rho2 <- nfRho rho
     ; return(Forall (windup ys2 (eqn2,rho2)))
     }
  

nfEqns xs = mapM f xs
  where f (Equality x y) = binaryLift Equality (nfTau x) (nfTau y)
  
nfTau ::  TyCh m => Tau -> m Tau
nfTau = normform
