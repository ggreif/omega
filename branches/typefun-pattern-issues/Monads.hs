-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Thu Nov  8 15:51:28 Pacific Standard Time 2007
-- Omega Interpreter: version 1.4.2

module Monads where

-- import IOExts
import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import System.IO(fixIO)
import System.IO.Unsafe(unsafePerformIO)
import Auxillary(Loc(..),displays)

-------------------------------------------------------------

instance Monad (Either String) where
  return x = Right x
  (>>=) (Right x) f = f x
  fail s = Left s

--------------------------------------------------------------
class Monad m => HasNext m where
  nextInteger :: m Integer
  resetNext   :: Integer -> m()

class Monad m => HasOutput m where
  outputString :: String -> m ()

class Monad m => HasFixpoint m where
  fixpoint :: (a -> m a) -> m a

class HasIORef m where
  newRef :: a -> m (IORef a)
  readRef :: IORef a -> m a
  writeRef :: IORef a -> a -> m ()

class Accumulates m z where
  extractAccum :: m a -> m (a,[z])
  injectAccum :: [z] -> m ()

class Monad m => TracksLoc m a | m -> a where
  position :: m Loc
  failN :: Loc -> Int -> String -> String -> m b

failP :: TracksLoc m a => String -> Int -> String -> m b
failP k n s = do { p <- position; failN p n k s}

-----------------------------------------------------
instance HasFixpoint IO where
  fixpoint = fixIO

instance HasOutput IO where
  outputString = putStrLn

instance HasNext IO where
  nextInteger = do { n <- readIORef counter; writeIORef counter (n+1); return n }
  resetNext m = writeIORef counter m

counter :: IORef Integer
counter = unsafePerformIO(newIORef 0)

reset:: HasNext m => m ()
reset = resetNext 0

instance HasIORef IO where
  newRef = newIORef
  readRef = readIORef
  writeRef = writeIORef

-------------------------------------------------------------

data Id x = Id x

instance Monad Id where
  return x = Id x
  (>>=) (Id x) f = f x

------------------------------

data Exception x
   = Ok x
   | Fail Loc        -- Source Location of Error
          Int        -- Severity or level of error
          String     -- kind of error
          String     -- message

instance Monad Exception where
  return x = Ok x
  (>>=) (Ok x) f = f x
  (>>=) (Fail loc n k s) f  = Fail loc n k s
  fail s = Fail Z 0 "" s

instance Functor Exception where
  fmap f (Ok x) = Ok (f x)
  fmap f (Fail loc n k s) = Fail loc n k s

-----------------------------------
data Env e x = Env (e -> x)

instance Monad (Env e) where
  return x = Env(\ e -> x)
  (>>=) (Env f) g = Env(\ e -> let Env h = g (f e)
                               in h e)


qq x yf =
  let Env f = x
      h e = let x = f e
                Env g = yf x
            in g e
  in Env h

type Map value = [(String,value)]

getEnv :: String -> (Env (Map v) v)
getEnv nm = Env(\ s -> find s)
  where find [] = error ("Name: "++nm++" not found")
        find ((s,n):m) = if s==nm then n else find m

runInNewEnv :: String -> Int -> (Env (Map Int) Int) -> (Env (Map Int) Int)
runInNewEnv s n (Env g) = Env(\ m -> g ((s,n):m))

------------------------------

data Store s x = St(s -> (x,s))

instance Monad (Store s) where
  return x = St(\ s -> (x,s))
  (>>=) (St f) g = St(\ s1 -> let (x,s2) = f s1
                                  St g' = g x
                              in g' s2)

get = St(\s -> (s,s))
put x = St(\ s -> ((),x))

runStore :: (Store s a) -> s -> (a,s)
runStore (St f) x = f x

tt x yf =
 let St f = x
     h s1 = let (x,s2) = f s1
                St g = yf x
                (y,s3) = g s2
            in (y,s3)
 in St h

getStore :: Num v => String -> (Store (Map v) v)
getStore nm = St(\ s -> find s s)
  where find w [] = (0,w)
        find w ((s,n):m) = if s==nm then (n,w) else find w m

putStore :: String -> v -> (Store (Map v) ())
putStore nm n = (St(\ s -> ((),build s)))
  where build [] = [(nm,n)]
        build ((s,v):zs) =
           if s==nm then (s,n):zs else (s,v):(build zs)

next :: Num n => Store n n
next = St(\ n -> (n,n+1))
-------------------------

data Mult x = Mult [x]

instance Monad Mult where
  return x = Mult[x]
  (>>=) (Mult zs) f = Mult(flat(map f zs))
     where flat [] = []
           flat ((Mult xs):zs) = xs ++ (flat zs)


zz x yf =
  let Mult xs = x
      ys = map yf xs
  in Mult (concat[ z | Mult z <- ys ])

---------------------------

data Output x = OP(x,String)

instance Monad Output where
  return x = OP(x,"")
  (>>=) (OP(x,s1)) f = let OP(y,s2) = f x in OP(y,s1 ++ s2)

printOutput:: String -> Output ()
printOutput s = OP((),s)

tag s x = do printOutput s
             x

--------------------------------------------
-- IO with catchable failure


newtype FIO x = FIO(IO (Exception x))
unFIO (FIO x) = x

instance Monad FIO where
  fail s = failFIO Z 0 s
  return x = FIO(return(Ok x))
  (>>=) (FIO a) g = FIO w
    where w = do { x <- a
                 ; case x of
                    Ok z -> unFIO(g z)
                    Fail loc n k s -> return(Fail loc n k s)}

instance Functor FIO where
  fmap f (FIO x) = FIO(fmap (fmap f) x)

failFIO loc n s = FIO(return(Fail loc n "" s))

fioFailD n disp xs = FIO(return(Fail Z n "" s))
  where (disp2,s) = displays disp xs

handleP :: (String -> Bool) -> Int -> FIO a ->
           (String -> FIO a) -> FIO a
handleP p m (FIO x) f = FIO w
  where w = do { a <- x
               ; case a of
                   Fail loc n k s ->
                       if (m > n) && (p k)
                          then unFIO(f s)
                          else return(Fail loc n k s)
                   ok -> return(ok)}

handle = handleP (\ _ -> True)

tryAndReport :: FIO a -> (Loc -> String -> FIO a) -> FIO a
tryAndReport (FIO x) f = FIO w
  where w = do { a <- x
               ; case a of
                   Fail loc n k s -> unFIO(f loc s)
                   ok -> return(ok)}

runFIO :: FIO x -> (Loc -> Int -> String -> IO x) -> IO x
runFIO (FIO x) f = do { a <- x
                      ; case a of
                          Ok z -> return z
                          Fail loc n k s -> f loc n s }

fixFIO :: (a -> FIO a) -> FIO a
fixFIO f = FIO(fixIO (unFIO . f . unRight))
    where unRight (Ok x) = x
          unRight (Fail loc n k s) = error ("Failure in fixFIO: "++s)


fio :: IO x -> FIO x
fio x = FIO(fmap Ok x)

write = fio . putStr
writeln = fio . putStrLn

readln :: String -> FIO String
readln prompt = fio (do {putStr prompt; getLine})

instance HasFixpoint FIO where
  fixpoint = fixFIO

instance HasNext FIO where
  nextInteger = fio nextInteger
  resetNext n = fio(resetNext n)

instance HasOutput FIO where
  outputString = writeln

instance HasIORef FIO  where
  newRef x = FIO(do { r <- newIORef x; return(Ok r)})
  readRef ref = FIO(do { r <- readIORef ref; return(Ok r)})
  writeRef ref x = FIO(writeIORef ref x >> return(Ok ()))

----------------------------------------------------------

data StEnv state env x = SE (state -> env -> (x,state))

instance Monad (StEnv s e) where
  return x = SE h
    where h s e = (x,s)
  (>>=) (SE f) g = SE(\ s1 e1 -> let (x,s2) = f s1 e1
                                     SE g' = g x
                                 in g' s2 e1)

newN :: StEnv Int a Int
newN = SE h
  where h s e = (s,s+1)

inenv :: env -> (StEnv s env x) -> StEnv s env x
inenv env m = SE h
  where h s e = h s env

getenv = SE h
  where h st env = (env,st)


-----------------------------------------------------------------
-----------------------------------------------------------------
-- Mtc is the Monad-for-type-checking. Its just an environment
-- monad layed over the FIO monad with the ability to acculumate.

forceMtc (Tc f) =
  let g _ _ _ = error "IN forceMtc"
  in case unsafePerformIO(runFIO (f undefined) g) of
      (a,ns) -> a

newtype Mtc e n a = Tc (e -> FIO (a,[n]))
unTc (Tc f) = f

mtc2fio env (Tc f) = do { (x,_) <- f env; return x }

instance Monad (Mtc e n) where
  return x = Tc f where f env = return(x,[])
  fail s = Tc f where f env = fail s
  (>>=) (Tc f) g = Tc h
     where h env = do { (a,ns1) <- f env
                      ; (b,ns2) <- unTc (g a) env
                      ; return(b,ns1++ns2)}

instance Functor (Mtc e n)  where
  fmap f x = do { a <- x; return(f a) }

handleTC :: (String -> Bool) -> Int -> Mtc e n a ->
            (String -> Mtc e n a) -> Mtc e n a
handleTC p m (Tc x) f = Tc w
  where w env = handleP p m (x env) (\ s -> unTc (f s) env)



fio2Mtc :: FIO a -> Mtc b c a
fio2Mtc x = Tc h
  where h env = do { ans <- x; return(ans,[]) }

-- Error reporting funcions in FIO

-- Report an error then die.
errF :: Loc -> Int -> String -> a
errF loc n s = error ("At "++show loc++"\n"++s)

-- Report an error, then continue with the continuation
report :: FIO a -> Loc -> String -> FIO a
report continue Z   message = do { writeln message; continue }
report continue loc message =
   do { writeln ("\n\n**** Near "++(show loc)++"\n"++message); continue }


------------------------------------------------
-- Some instance Declarations

instance HasFixpoint (Mtc e n) where
  fixpoint = error "No fixpoint for TC"

instance HasNext (Mtc e n) where  -- Supports a unique supply of Integers
  nextInteger = Tc h where h env = fio(do { n <- nextInteger;return(n,[])})
  resetNext n = Tc h where h env = fio(do { resetNext n; return((),[])})

instance HasOutput (Mtc e n) where -- Supports Output of Strings
  outputString s = Tc h where h env = writeln s >> return((),[])

instance HasIORef (Mtc e n) where
  newRef v = lift (newIORef v)
  readRef r = lift (readIORef r)
  writeRef r v = lift (writeIORef r v)

instance Accumulates (Mtc e n) n where
  extractAccum (Tc f) = Tc g
    where g env = do { (a,ns) <- f env; return((a,ns),[])}
  injectAccum ns = Tc g
    where g env = return((),ns)


-------------------------------------------------------

-- Moving back and forth between IO and Mtc

runTC :: Show n => e -> Mtc e n a -> IO a
runTC env (Tc f) =
   do { --let env = TcEnv { var_env = listToFM []
        --                , generics = []
        --                , verbose = False }
      ; (a,out) <- runFIO (f env) (\ loc n s -> error s)
      ; putStrLn ("Need = "++show out)
      ; return a }

-- Lift an IO action into Mtc, ignores the environment
-- and always succeeds and accumulates nothing

lift :: IO a -> Mtc e n a
lift st = Tc (\env -> do { r <- fio st; return(r,[]) })

testTC :: e -> Mtc e n a -> a
testTC env (Tc f) = unsafePerformIO
  (do { (a,out) <- runFIO (f env) (\ loc n s -> error s)
      ; return a })


traceSh s x = unsafePerformIO(putStrLn ("\n--- Trace ---\n"++s++show x))

traceShA s x = seq (unsafePerformIO(putStrLn ("\n--- Trace ---\n"++s++show x))) x

traceStr x y = seq (unsafePerformIO(putStrLn ("\n--- Trace ---\n"++x))) y
