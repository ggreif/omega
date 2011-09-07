-- Time-stamp: <2010-03-31 20:47:48 cklin>

module Monad where

import Control.Monad (liftM, mapM_, when)
import Data.Maybe (isJust)

import Types
import Common

type EndoTi a = a -> Ti a

--------- Type inference monad and its combinators

-- Type inference state consists of a sequence number for generating
-- fresh meta type variables and a list of strings that record diagnosis
-- and error messages in reverse chronological order.

type TiS a = (Int, [String], a)
type TiM a = TiS (Maybe a)

newtype Ti a =
    Ti { unTi :: Int -> TiM a }

instance Monad Ti where
    fail w   = Ti $ \s -> (s, ["ERROR: " ++ w], Nothing)
    return a = Ti $ \s -> (s, [], Just a)
    m >>= k  = Ti $ \s -> mapJust bind (unTi m s) where
        bind (s1, w1, v1) = (s2, w2 ++ w1, v2)
            where (s2, w2, v2) = unTi (k v1) s1

die :: Ti a
die = Ti $ \s -> (s, [], Nothing)

mapJust :: (TiS a -> TiM b) -> TiM a -> TiM b
mapJust _ (s, w, Nothing) = (s, w, Nothing)
mapJust f (s, w, Just a)  = f (s, w, a)

runTi :: Ti a -> Int -> a
runTi m s = a where (_, _, Just a) = unTi m s

-- Arrest any failure in a monadic computation.  The arrested
-- computation returns Nothing if a failure occurred.

catchTi :: Ti a -> Ti (Maybe a)
catchTi m = Ti $ m1 where
    m1 s = (s1, w, Just x)
        where (s1, w, x) = unTi m s

succeedTi :: Ti a -> Ti Bool
succeedTi = liftM isJust . catchTi . catchNotes

-- Unleash the inner Maybe monad.  Warning: all messages in the
-- attempted computations, error or otherwise, are discarded.  To
-- preserve the messages, set the verbose flag to True.

verbose = False

attemptTi :: [Ti a] -> Endo (Ti a)
attemptTi ax final = attempt ax where
    attempt [] = final
    attempt (m:mx) =
        do (w, result) <- arrestTi m
           when verbose (mapM_ (mesg . ("o " ++)) w)
           case result of
             Just a -> return a
             Nothing -> attempt mx

-- Generate fresh meta type variables, or just the serial number.

newMetaTv :: Ti Type
newMetaTv = liftM TyMeta newMetaIndex

newMetaIndex :: Ti Int
newMetaIndex = Ti $ \s -> (s+1, [], Just s)

freshenTv :: [a] -> Ti [Type]
freshenTv = mapM (const newMetaTv)

freshenIndex :: [a] -> Ti [Int]
freshenIndex = mapM (const newMetaIndex)

freshenTyCon :: EndoTi Type
freshenTyCon (TyCon tc ax) = liftM (TyCon tc) (freshenTv ax)
freshenTyCon v = bug ("Non-constructor type " ++ show v)

renameToNew :: [Int] -> Ti Rename
renameToNew xs = liftM (toMap . zip xs) (freshenIndex xs)

-- Write to or read from the internal messages store.  Unlike the fail
-- function, the mesg function writes a message without declaring a
-- failure.  The catchNotes function erases all messages, even if the
-- transformed computation fails.

mesg :: String -> Ti ()
mesg w = Ti $ \s -> (s, [w], Just ())

replay :: [String] -> Ti ()
replay = mapM_ mesg

arrestTi :: Ti a -> Ti ([String], Maybe a)
arrestTi = catchNotes . catchTi

catchNotes :: Ti a -> Ti ([String], a)
catchNotes m = Ti m1 where
    m1 s = (s1, [], liftM attach x)
        where (s1, w, x) = unTi m s
              attach a = (reverse w, a)

-- To ensure freshness of newly generated type variables in the presence
-- of hard-coded type variables in the Ti computation (for example, in
-- unit tests), we choose 100 as the initial sequence number.  The
-- programmer should make sure that all hard-coded meta type variables
-- have index numbers < 100.

initSeq :: Int
initSeq = 100

trapTi :: Ti a -> Maybe a
trapTi m = runTi (catchTi m) initSeq

examineTi :: Ti a -> IO (Maybe a)
examineTi m =
    let (w, v) = runTi (arrestTi m) initSeq
    in do mapM_ putStrLn w
          return v

