{-# LANGUAGE FlexibleContexts
  , UndecidableInstances
  #-}
module Value where
import Auxillary(plist,plistf)
import Monads(FIO,fio,HasNext(..))
import Monad
import Syntax
import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import Bind
import RankN(Z,postscript,DocReady(..))
import SyntaxExt
import Text.PrettyPrint.HughesPJ(Doc,text)

-----------------------------------------------
{- These are now defined in the Syntax file

data Ev = Ev [(Var,V)] (V,V,V)

showenv (Ev xs) =
  "Ev with \n   "++show (map fst xs)

type EnvFrag = [(Var,V)]
type Perm = [(Name,Name)]

compose = Vprimfun "(.)" (\

data V
  = Vlit Lit
  | Vsum Inj V
  | Vprod V V
  | Vprimfun String (V -> FIO V)
  | Vfun [Pat] Exp Ev
  | Vf (V -> FIO V) (Ev -> V) (Perm -> V)
  | Vcon (Var,SynExt String) [V]
  | Vpat Var ([Pat]->Pat) V
  | Vlazy (IORef (Either (FIO V) V))
  | Vcode Exp Ev
  | Vswap Perm V
  | Vfio Perm (FIO V)
  | Vptr Perm Integer (IORef (Maybe V))
  | VChrSeq String
  | Vparser (Parser V)
  | Vbottom

--------------------------------------
-}

instance DocReady V where
  dDoc d x = (d,text (show x))

class Push t where
  push :: Ev -> t -> t

instance Show V => Push V where
  push e (Vlit l) = Vlit l
  push e (Vsum inj v) = Vsum inj (push e v)
  push e (Vprod u v) = Vprod (push e u) (push e v)
  push e (Vprimfun s f) = Vprimfun s f
  push e x@(Vfun _ _ _) = error ("Push not defined for: "++show x)
  push e (Vf f g h) = g e
  push e (Vcon c vs) = Vcon c (map (push e) vs)
  push e (Vpat nm f v) = Vpat nm f (push e v)
  push e (Vswap p v) = Vswap p (push e v)
  push e Vbottom = Vbottom
  push e (VChrSeq s) = VChrSeq s
  push e (Vparser p) = Vparser p
  push e x = error ("Push not defined for: "++show x)

-- This instance of Swap for V is somewhat lazy.
-- It only pushes the permutation under one constructor.

instance Swap V where
  swaps [] v = v
  swaps cs (Vlit (Symbol x)) = (Vlit (Symbol (swaps cs x)))
  swaps cs (Vlit x)      = Vlit x
  swaps cs (Vswap ds v)  = swaps (cs++ds) v
  swaps cs (Vsum inj x)  = Vsum inj (Vswap cs x)
  swaps cs (Vprod x y)   = Vprod (Vswap cs x) (Vswap cs y)
  swaps cs (Vprimfun s g)  = Vprimfun s g
  swaps cs (Vcon n vs)   = Vcon n (map (Vswap cs) vs)
  swaps cs (Vpat nm g v) = Vpat nm g (Vswap cs v)
  swaps cs (Vlazy ds ref)   = Vlazy (cs++ds) ref
  swaps cs (Vfun v e env)= Vfun (swaps cs v) (swaps cs e) (swaps cs env)
  swaps cs (Vf f push swap) = swap cs
  swaps cs (Vcode e env) = Vcode (swaps cs e) (swaps cs env)
  swaps cs (Vfio ds comp) = Vfio (cs++ds) comp
  swaps cs (Vptr ds n ref) = Vptr (cs++ds) n ref
  swaps cs (VChrSeq s) = VChrSeq s
  swaps cs (Vparser p) = Vparser p
  swaps cs Vbottom = Vbottom

instance Swap Ev where
  swaps [] ev = ev
  swaps cs (Ev xs m) = Ev (swaps cs xs) (swaps cs m)

instance Swap Lit where
  swaps [] x = x
  swaps cs (Symbol nm) = Symbol (swaps cs nm)
  swaps cs x = x

instance Swap Pat where
  swaps [] x = x
  swaps cs (Plit x) = Plit (swaps cs x)
  swaps cs (Pvar v) = Pvar (swaps cs v)
  swaps cs (Pprod x y) = Pprod (swaps cs x) (swaps cs y)
  swaps cs (Psum inj y) = Psum inj (swaps cs y)
  swaps cs (Pexists y) = Pexists (swaps cs y)
  swaps cs (Paspat x y) = Paspat (swaps cs x) (swaps cs y)
  swaps cs Pwild = Pwild
  swaps cs (Pcon x y) = Pcon(swaps cs x) (map (swaps cs) y)

instance Swap Exp where
  swaps [] e = e
  swaps cs (Var v) = Var (swaps cs v)
  swaps cs (Lit l) = Lit (swaps cs l)
  swaps cs (Sum inj y) = Sum inj (swaps cs y)
  swaps cs (Prod x y) = Prod (swaps cs x) (swaps cs y)
  swaps cs (App x y) = App (swaps cs x) (swaps cs y)
  swaps cs (Lam ps e fs) = Lam (swaps cs ps) (swaps cs e) (swaps cs fs)
  swaps cs (Let ds e) = Let (swaps cs ds) (swaps cs e)
  swaps cs (Circ vs e ds) = Circ (swaps cs vs) (swaps cs e)(swaps cs ds)
  swaps cs (Case e ms) = Case (swaps cs e) (map (swapsMatch cs) ms)
  swaps cs (Do ss) = Do (map (swaps cs) ss)
  swaps cs (CheckT e) = CheckT (swaps cs e)
  swaps cs (Lazy e) = Lazy (swaps cs e)
  swaps cs (Exists e) = Exists (swaps cs e)
  swaps cs (Under e f) = Under (swaps cs e) (swaps cs f)
  swaps cs (Bracket e) = Bracket (swaps cs e)
  swaps cs (Escape e) = Escape(swaps cs e)
  swaps cs (Run e) = Run (swaps cs e)
  swaps cs (Reify s v) = Reify s (swaps cs v)

swapsMatch [] trip = trip
swapsMatch cs (loc,pat,body,ds) =
   (loc,swaps cs pat, swaps cs body, swaps cs ds)

instance (Swap p, Swap e, Swap d) => Swap (Stmt p e d) where
  swaps [] s = s
  swaps cs (BindSt l p e) = BindSt l (swaps cs p) (swaps cs e)
  swaps cs (LetSt l ds) = LetSt l (map (swaps cs) ds)
  swaps cs (NoBindSt l e) = NoBindSt l (swaps cs e)

instance Swap e => Swap (Body e) where
  swaps [] b = b
  swaps cs (Guarded pairs) = Guarded (swaps cs pairs)
  swaps cs (Normal e) = Normal(swaps cs e)

instance Swap Dec where
  swaps [] d = d
  swaps cs (Fun loc v h ms) = Fun loc (swaps cs v) h (map (swapsMatch cs) ms)
  swaps cs (Val loc p b ds) = Val loc (swaps cs p) (swaps cs b) (swaps cs ds)
  swaps cs (Pat loc v vs p) = Pat loc (swaps cs v) (swaps cs vs) (swaps cs p)
  swaps cs (TypeSig loc v t) = TypeSig loc v t -- What do we do here?
  swaps cs (Prim loc nm t) = Prim loc nm t
  swaps cs (Data loc b n v sig vs cons ds ) = Data loc b n v sig vs cons ds
  swaps cs (GADT x1 x2 x3 x4 x5 x6 x7) = (GADT x1 x2 x3 x4 x5 x6 x7)
  swaps cs (TypeSyn loc nm args ty) = TypeSyn loc nm args ty
  swaps cs (Flag x y) = Flag (swaps cs x) (swaps cs y)
  swaps cs (Reject s d) = Reject s (swaps cs d)
  swaps cs (AddTheorem loc xs) = AddTheorem loc (swaps cs xs)


---------------------------------------
vTuple [] = Vlit Unit
vTuple [v] = v
vTuple [x,y] = Vprod x y
vTuple (x:xs) = Vprod x (vTuple xs)

vint n = Vlit(Int n)

trueExp  = Vcon (Global "True",Ox) []
falseExp = Vcon (Global "False",Ox) []

--------- instances for Ev --------------------------------------------

showEnv (Ev xs m) =
  "Ev "++ plistf fx "[" xs "," "]"
  where fx (x,y) = show x ++ "=" ++ show y


instance Show Ev where
  show = showEnv

--------- instances for V ---------------------------------------------------

showSynPair (p@(Vcon (Global c,ext) [x,y])) | pairProd c ext =
   plistf show "(" (collect p) "," ")" ++ postscript (synKey ext)
   -- "(" ++ show x ++","++show y++")"++postscript (synKey ext)
  where collect (Vcon (Global c,ext) [x,y]) | pairProd c ext = x: collect y
        collect y = [y]
showSynPair v = showVcon v

showSynList (Vcon (Global c,ext) []) | listNil c ext = "[]" ++ postscript (synKey ext)
showSynList (Vcon (Global c,ext) [x,xs]) | listCons c ext = "[" ++ show x ++ f xs
    where f (Vlazy cs _) = " ...]"
          f (Vcon (Global c,ext) [x,xs])| listCons c ext = "," ++ show x ++ f xs
          f (Vcon (Global c,ext) []) | listNil c ext = "]" ++ postscript (synKey ext)
          f (Vswap cs u) = f (swaps cs u)
          f v = showVcon v
showSynList v = showVcon v

showSynLeftList (Vcon (Global c,ext) []) | leftListNil c ext = "[]" ++ postscript (synKey ext)
showSynLeftList (Vcon (Global c,ext) [xs, x]) | leftListCons c ext = "[" ++ show x ++ f xs
    where f (Vlazy cs _) = " ...]"++tag
          --f (Vcon (Global c,ext) []) | listListNil c ext = ""
          f v = showVcon v
          tag = postscript (synKey ext)
showSynLeftList v = showVcon v

showSynRecord (Vcon (Global c,ext) [])         | recordNil c ext = "{}" ++ postscript (synKey ext)
showSynRecord (Vcon (Global c,ext) [tag,x,xs]) | recordCons c ext   = "{" ++ show tag++"="++show x ++ f xs
    where f (Vlazy cs _) = " ...}"
          f (Vcon (Global c,ext) [tag,x,xs])   | recordCons c ext = "," ++ show tag++"="++show x ++ f xs
          f (Vcon (Global c,ext) [])           | recordNil c ext  = "}" ++ postscript (synKey ext)
          f (Vswap cs u) = f (swaps cs u)
          f v = showVcon v
showSynRecord v = showVcon v


showSynNat (Vcon (Global c,ext) []) | natZero c ext = "0" ++ postscript (synKey ext)
showSynNat (Vcon (Global c,ext) [x])| natSucc c ext = (f 1 x)++ postscript (synKey ext)
      where f n (Vcon (Global c,ext) [])  | natZero c ext = show n
            f n (Vcon (Global c,ext) [x]) | natSucc c ext = f (n+1) x
            f n (Vswap cs u) = f n (swaps cs u)
            f n (Vlazy cs _) = "("++show n++"+ ...)"
            f n v = "("++show n++"+"++show v++")"
showSynNat v = showVcon v


showSynTick (Vcon (Global c,ext) [x])     | tickSucc c ext = (f 1 x)++ postscript (synKey ext)
      where f n (Vcon (Global c,ext) [x]) | tickSucc c ext = f (n+1) x
            f n (Vswap cs u) = f n (swaps cs u)
            f n (Vlazy cs _) = "("++show n++"+ ...)"
            f n v = "("++show v++"`"++show n++")"
showSynTick v = showVcon v

tim = Vcon (Global "A",wExt) [] 

showVcon (Vcon (c,_) vs) =
  case vs of
   [] -> show c  -- ++ g exts
   vs -> "("++show c++plistf show " " vs " " ")"

instance Show V where
  show (Vlit x) = show x
  show (v @ (Vsum inj x)) =
    case boolV v of
      Nothing -> "("++show inj++" "++show x++")"
      Just t -> if t then "True" else "False"
  show (v@(Vprod x y)) =  plistf show "(" (collect v []) "," ")"
    where collect (Vprod x y) ans = collect y (x:ans)
          collect other ans = reverse( (other : ans))
    
    --  "("++show x++","++show y++")"
  show (Vprimfun s f) = "<primfun "++s++">"
  show (Vfun p e (Ev xs _)) = "(fn" ++ show (map fst xs)++")"
  show (Vf f push swap) = "<fn>"
  show (Vlazy cs m) = " ..."
  show (Vpat nm f g) = (show nm)
  show (Vcon (Global "[]",ext) []) | normalList ext = "[]"
  show (VChrSeq s) = "#"++show s
  -- special case for [Char]
  show (Vcon (Global ":",ext) [Vlit (Char c),xs]) | normalList ext = "\""++[c]++ f xs
      where f (Vlazy cs _) = "...\""
            f (Vcon (Global ":",ext) [Vlit(Char c),xs]) | normalList ext = [c] ++ f xs
            f (Vcon (Global ":",ext) [Vlazy cs _,xs])   | normalList ext = "..."++f xs
            f (Vcon (Global "[]",ext) [])               | normalList ext = "\""
            f (Vswap cs u) = f (swaps cs u)

  show (v@(Vcon (Global c,ext) _)) | pairProd c ext = showSynPair v
  show (v@(Vcon (Global c,ext) _)) | natExt c ext = showSynNat v
  show (v@(Vcon (Global c,ext) _)) | listExt c ext = showSynList v
  show (v@(Vcon (Global c,ext) _)) | leftListExt c ext = showSynLeftList v
  show (v@(Vcon (Global c,ext) _)) | recordExt c ext = showSynRecord v
  show (v@(Vcon (Global c,ext) _)) | tickSucc c ext = showSynTick v
  show (Vcode e (Ev xs _)) = "[| " ++ show e ++" |]" -- " | "++ free ++ " |]"
      where free = plistf show "" (map fst xs) "," ""
  show (Vswap cs u) =  show (swaps cs u)
                       --"(Vswap "++show cs ++" "++ show u++")"
  show (Vfio cs comp) = "<IO action>"
  show (Vptr cs n ref) = "<ptr "++show n++">"
  show (Vparser p) = "<parser>"
  show Vbottom = "**undefined**"
  show (v@(Vcon (_,_) _)) = showVcon v
 

listV :: Monad m => V -> m [V]    -- Particularly useful when m is Maybe
listV (Vcon (Global "[]",ext) [])    | normalList ext = return []
listV (Vcon (Global ":", ext) [x,y]) | normalList ext = do {xs <- listV y; return(x:xs) }
listV (v@(Vlazy cs m)) = return[v]
listV _ = fail "Not a List"


boolV :: Monad a => V -> a Bool  -- Particularly useful when m is Maybe
boolV (Vsum L (Vlit Unit)) = return False
boolV (Vsum R (Vlit Unit)) = return True
boolV _ = fail "Not a Bool"


showVlist [] = "[]"
showVlist (cs @ (Vlit (Char _):_)) = --Its a String
          show (map (\ (Vlit (Char c)) -> c) cs)
showVlist vs = "[" ++ f vs
  where f [] = "]"
        f [v,Vlazy _ _] = show v ++ " ...]"
        f [v] = show v ++ "]"
        f (v:vs) = show v ++ "," ++ f vs

-- If you need to see the constructors for debugging use this function

pv v = help v
 where help (Vlazy cs comp) = "(Lazy ...)"
       help (Vlit l) = "(Vlit "++(show l)++")"
       help (Vsum inj x) = "(Vsum "++show inj++" "++pv x++")"
       help (Vprod x y) = "(Vprod "++pv x++","++pv y++")"
       help (Vprimfun s _) = "(Vprimfun "++s++")"
       help (Vfun p body env) = "(fn)"
       help (Vf f push swap) = "(Vf f g h)"
       help (Vcon (n,ext) vs) = "(Vcon "++show n++" ("++show ext++") ["++plistf pv " " vs "," "])"
       help (Vpat n f g) = "(Vpat "++show n++")"
       help (Vcode e re) = "(Code "++show e++")"
       help (Vswap cs u) = "(Vswap "++show cs ++" "++ pv u++")"
       help (Vfio cs comp) = "(Vfio action)"
       help (Vptr cs n ref) = "(Vptr "++show n++" ref)"
       help (VChrSeq s) = "(VChrSeq "++s++")"
       help (Vparser p) = "(Vparser)"
       help Vbottom = "(Vbottom)"
----------------------------------------------------

mkSymbol s = Vlit(Symbol s)

------------------------------------------------------------------
-- Suppose I have a function that needs to analyze the structure
-- of a value to proceed. The constructors Vlazy and Vswap hide
-- this structure. So use the function "analyzeWith" to expose the structure.

analyzeWith :: (V -> FIO a) -> V -> FIO a
analyzeWith f v = downSwap [] f v


downSwap cs f (Vlazy ds ref) = do { a <- down ref; downSwap (cs++ds) f a }
downSwap cs f (Vswap ds v) = downSwap (cs++ds) f v
downSwap cs f Vbottom = fail "Error -- Something pulled on undefined"
downSwap [] f v = f v
downSwap cs f v = f (swaps cs v)

-------------------------------------------------------
-- Here is how to deal with the lazy constructor of Values

-- Make a value from a computation. Don't run the computation
-- until the value is pulled on.

vlazy c = do { r <- fio(newIORef (Left c)); return(Vlazy [] r) }

type Ref a = (IORef (Either (FIO a) a))

down :: Ref V -> FIO V
down ref =
  do { x <- fio(readIORef ref)
     ; case x of
         Left m ->
           do { v <- m
              ; u <- case v of
                      Vlazy cs r2 -> do { x <- down r2; return (swaps cs x) }
                      u -> return u
              ; fio(writeIORef ref (Right u))
              ; return u }
         Right v -> return v
     }

-----------------------------------------------------------------
-- Primitive operations on Ptrs

newPtr :: V
newPtr = Vfio [] action
  where action =
         do { r <- fio(newIORef Nothing);
            ; n <- nextInteger
            ; return(Right (Vcon (Global "Nil",Ox) [Vptr [] n r]))}

myIo :: V -> FIO (Either String V)
myIo v = (return(Right v))

initPtr :: V
initPtr = Vprimfun "initPtr" (analyzeWith f) where
  f ptr@(Vptr cs n ref) = return(Vprimfun name g) where
     name = ("initPtr "++show ptr)
     g b = return(Vfio [] comp) where
         comp = do { x <- fio(readIORef ref)
                   ; case x of
                      Nothing -> do { fio (writeIORef ref (Just b))
                                    ; myIo(Vcon (Global "Eq",Ox) [])}
                      Just v -> return(Left "initPtrFails")}
  f v = fail ("Non Ptr as argument to initPtr: "++show v)

writePtr :: V
writePtr = Vprimfun "writePtr" (analyzeWith f) where
  f ptr@(Vptr cs n ref) = return(Vprimfun name g) where
     name = ("writePtr "++show ptr)
     g b = return(Vfio [] comp) where
         comp = do { fio (writeIORef ref (Just b))
                   ; myIo(Vlit Unit) }
  f v = fail ("Non Ptr as argument to writePtr: "++show v)

readPtr :: V
readPtr = Vprimfun "readPtr" (analyzeWith f) where
  f ptr@(Vptr cs n ref) = return(Vfio [] comp) where
     comp = do { x <- fio(readIORef ref)
               ; case x of
                  Nothing -> myIo(Vcon (Global "Nothing",Ox) [])
                  Just v ->  myIo(Vcon (Global "Just",Ox) [swaps cs v])}
  f v = fail ("Non Ptr as argument to readPtr: "++show v)

nullPtr :: V
nullPtr = Vprimfun "nullPtr" (analyzeWith f) where
  f ptr@(Vptr cs n ref) = return(Vfio [] comp) where
     comp = do { x <- fio(readIORef ref)
               ; case x of
                  Nothing -> myIo(Vcon (Global "True",Ox) [])
                  Just v ->  myIo(Vcon (Global "False",Ox) [])}
  f v = fail ("Non Ptr as argument to nullPtr: "++show v)


samePtr :: V
samePtr = Vprimfun "samePtr" (analyzeWith f) where
  f ptr1@(Vptr cs n ref) = return(Vprimfun name (analyzeWith g)) where
     name = ("samePtr "++show ptr1)
     g ptr2@(Vptr cs2 n2 ref2)  = return(Vfio [] comp) where
         comp = if ref == ref2
                   then myIo(Vcon (Global "Eq",Ox) [])
                   else return(Left "samePtrFails")
     g v = fail ("Non Ptr as 2nd argument to samePtr: "++show v)
  f v = fail ("Non Ptr as 1st argument to samePtr: "++show v)

------------------------------------------------------
-- Labels

newtype Label tag = Label String

instance Show (Label tag)  where
  show (Label x) = "`" ++ (show x)

instance Eq (Label tag)  where
  (Label x) == (Label y) = x==y

tagOfLabel :: Label t -> t
tagOfLabel x = error "Someone pulled on tagOfLabel"

data HiddenLabel = Hidden (Label String)

instance Show HiddenLabel where
 show (Hidden l) = "(Hidden "++show l++")"

------------------------------------------

newtype Equal a b = Eq ()

instance Show (Equal a b) where
  show (Eq _) = "Eq"

instance Eq (Equal a b) where
  (Eq _) == (Eq _)= True

leftEqual :: Equal a b -> a
leftEqual x = error "Someone pulled on leftEqual"

rightEqual :: Equal a b -> b
rightEqual x = error "Someone pulled on leftEqual"
