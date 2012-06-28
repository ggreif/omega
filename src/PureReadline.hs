-----------------------------------------------------------
-- |
-- Module      :  System.Console.PureReadline
-- Copyright   :  Anders Carlsson 2004, 
--                Bjorn Bringert 2004
-- License     :  BSD-style
--
-- Maintainer  :  Bjorn Bringert, bjorn@bringert.net
-- Stability   :  experimental
-- Portability :  non-portable
-- 
-- Extended and modified by Tim Sheard for use in Omega
--  June 17, 2009
--
-- A simple readline replacement module in pure Haskell.
--
-- TODO
--
-- * Support non-vt100 terminals
--
-- * Support non-posix pathnames in tab completion
--
-- * Support .inputrc
--
-- * Show alternatives when completion is ambiguous
--
-- * Restore terminal settings when interrupted
--
-- * ifdef away echoing stuff for Hugs support
--
-- * Support undo
--
-- * Support yanking (pasting) 
--
-----------------------------------------------------------
module PureReadline (readline, addHistory,setCompletionEntryFunction) where

import Control.Exception (finally)
import Control.Monad
import Data.Char (isSpace)
import Data.IORef
import Data.List (isPrefixOf, inits)
import System.IO
import System.IO.Unsafe (unsafePerformIO)
import System.Directory (getDirectoryContents, doesDirectoryExist)
--import System.FilePath.Posix (pathSeparator)
pathSeparator = '/'

data Command 
    = Move Cursor
    | Accept
    | DeletePrev
    | DeleteCurr
    | DeleteToEnd
    | Char Char
    | HistoryPrev
    | HistoryNext
    | Complete
    | EndOfFile
    | Undo
    deriving (Eq, Ord, Show, Read)

data Cursor 
    = Previous
    | Next
    | Home
    | End
      deriving (Eq, Ord, Show, Read)

type Commands = 
    [(String, Command)]

data ReadState = 
    ReadState { chars :: (String, String),
		historyState :: ([String],[String]),
		gotEOF :: Bool }
    deriving (Eq, Ord, Show, Read)

data Completion = FullCompletion String
		| PartialCompletion String
		| AmbiguousCompletion [String]
		| NoCompletion
		  deriving (Eq, Ord, Show, Read)

debug s = return ()
--debug s = appendFile "debug.log" (s ++ "\n")

--
-- * Escape sequences
--

prevStr = "\ESC[D"
nextStr = "\ESC[C"

commands :: Commands
commands = 
    [("\n",      Accept),        -- Enter
     ("\ESC[D",  Move Previous), -- left arrow
     ("\STX",    Move Previous), -- C-b
     ("\ESC[C",  Move Next),     -- right arrow
     ("\ACK",    Move Next),     -- C-f
     ("\SOH",    Move Home),     -- C-a
     ("\ESC[H",  Move Home),     -- Home
     ("\ENQ",    Move End),      -- C-e
     ("\ESC[F",  Move End),      -- End
     ("\b",      DeletePrev),    -- Backspace
     ("\DEL",    DeletePrev),    -- Backspace
     ("\ESC[3~", DeleteCurr),    -- Del
     ("\v",      DeleteToEnd),   -- C-k
     ("\ESC[A",  HistoryPrev),   -- up arrow
     ("\ESC[B",  HistoryNext),   -- down arrow
     ("\t",      Complete),      -- tab
     ("\EOT",    EndOfFile),     -- C-d
     ("\US",     Undo),          -- C-_
     ("\CAN\NAK", Undo)          -- C-x C-u
    ]

--
-- * Utilities
--

atLeast :: Int -> [a] -> Bool
atLeast n _ | n <= 0 = True
atLeast n [] = False
atLeast n (x:xs) = atLeast (n-1) xs

-- FIXME: not very efficient
commonPrefix :: Eq a => [[a]] -> [a]
commonPrefix [] = []
commonPrefix xs@(x:_) = last [p | p <- inits x, all (p `isPrefixOf`) xs]

--
-- * List with a cursor
--

type CursorList a = ([a],[a])

mkCursorList :: [a] -> CursorList a
mkCursorList xs = (reverse xs,[])

toList :: CursorList a -> [a]
toList (xs,ys) = reverse xs ++ ys

previous :: CursorList a -> CursorList a
previous (x:xs,ys) = (xs,x:ys)

next :: CursorList a -> CursorList a
next (xs,y:ys) = (y:xs,ys)

toStart :: CursorList a -> CursorList a
toStart l = ([], toList l)

toEnd :: CursorList a -> CursorList a
toEnd (xs,ys) = (xs ++ reverse ys, [])

insert :: [a] -> CursorList a -> CursorList a
insert x (xs,ys) = (reverse x ++ xs, ys)

set :: [a] -> CursorList a -> CursorList a
set xs _ = mkCursorList xs

setNext :: a -> CursorList a -> CursorList a
setNext x (xs,_:ys) = (xs, x:ys)

--
-- * Edit state
--

initState :: IO ReadState
initState = 
    do
    h <- getHistory
    return ReadState { chars = mkCursorList "", 
		       historyState = (h,[""]),
		       gotEOF = False }

modifyChars :: ReadState -> ((String,String) -> (String,String)) -> ReadState
modifyChars st@(ReadState{ chars = cs}) f = st{ chars = f cs }

modifyHistoryState :: ReadState -> (([String],[String]) -> ([String],[String])) -> ReadState
modifyHistoryState st@(ReadState{ historyState = hs }) f = st { historyState = f hs }

--
-- * History
--

type History = [String]




{-# NOINLINE history #-}
history :: IORef History
history = unsafePerformIO (newIORef initHistory)

initHistory :: History
initHistory = []

addHistory :: String -> IO ()
addHistory str = modifyIORef history (str:)

getHistory :: IO History
getHistory = readIORef history

--
-- * Cursor movement
--

moveLeft :: Int -> IO ()
moveLeft n = putStr $ concat $ replicate n prevStr

moveRight :: Int -> IO ()
moveRight n = putStr $ concat $ replicate n nextStr

replaceLine :: String -> String -> IO ()
replaceLine old new = 
    do moveLeft (length old)
       let sp = replicate (length old - length new) ' '
       putStr (new ++ sp)
       moveLeft (length sp)

--
-- * Tab completion
--

getCompletion :: String -> IO Completion
getCompletion pref =
    do
    completionsF <- readIORef tabCompletionFun
    cs <- completionsF pref
    debug ("Possible completions for " ++ show pref ++ ": " ++ show cs)
    case cs of
	    [] -> return NoCompletion
	    [x] -> do
		   isDir <- doesDirectoryExist x
		   return $ if isDir then
		      PartialCompletion (x ++ [pathSeparator])
		    else
		      FullCompletion x
	    xs -> case commonPrefix xs of
				       "" -> return $ AmbiguousCompletion xs
				       x  -> return $ PartialCompletion x

-- FIXME: ignore hidden files?
getCompletions :: String -> IO [String]
getCompletions pref = return[pref]
{-
    do
    let (d,f) = getDirFile pref
	d' = if d == "" then "." else d
    fs <- getDirectoryContents d'
    return [ d ++ f' | f' <- fs, f `isPrefixOf` f']
-}

{-# NOINLINE tabCompletionFun #-}
tabCompletionFun = unsafePerformIO (newIORef getCompletions)
setCompletionEntryFunction f = writeIORef tabCompletionFun f


--
-- * Input to Command
--
     
getCommand :: Commands -> IO Command
getCommand cs = 
    do c <- hGetChar stdin
       -- FIXME: remove
       debug (show c)
       let cs' = [(ss, command) | ((s:ss), command) <- cs, s == c]
       case cs' of 
		[] -> return $ Char c
		[("", command)] -> return command
		_ -> getCommand cs'


commandLoop :: ReadState -> IO ReadState
commandLoop st@(ReadState{chars = cs@(xs,ys), historyState = (h1,h2) }) =
    do command <- getCommand commands
       debug (show (historyState st))
       case command of
		    Move Previous | not (null xs) ->
			   do moveLeft 1
			      loop previous
		    Move Next | not (null ys) ->
			   do moveRight 1
			      loop next
		    Move Home ->
			   do moveLeft (length xs)
			      loop toStart
		    Move End ->
			   do moveRight (length ys)
			      loop toEnd
		    Char c -> 
			   do putStr (c:ys)
			      moveLeft (length ys)
			      loop $ insert [c]
		    DeletePrev | not (null xs) ->
			   do moveLeft 1
			      let ys' = ys ++ " "
			      putStr ys'
			      moveLeft (length ys')
			      loop $ \ (_:xs, ys) -> (xs, ys)
		    DeleteCurr | not (null ys) ->
			   do let ys' = drop 1 ys ++ " "
			      putStr ys'
			      moveLeft (length ys')
			      loop $ \ (xs, _:ys) -> (xs, ys)
		    DeleteToEnd ->
			   do let n = length ys
			      putStr $ replicate n ' '
			      moveLeft n
			      loop $ \ (xs,_) -> (xs, "")
		    HistoryPrev | not (null h1) ->
			   do let h = head h1
			      replaceLine xs h
			      loopHistory (set h) (previous . setNext (toList cs))
		    HistoryNext | atLeast 2 h2 ->
			   do let _:h:_ = h2
			      replaceLine xs h
			      loopHistory (set h) (next . setNext (toList cs))
		    Accept -> 
			   do putStrLn ""
			      return st
		    Complete -> 
			   do
			   let pref = reverse $ takeWhile (not.isSpace) xs
			   x <- getCompletion pref
			   case x of 
				  FullCompletion s -> do 
						let s' = drop (length pref) s ++ " "
						putStr (s'++ys)
						debug ("completing " ++ show pref ++ " to " ++ show s)
						moveLeft (length ys)
						loop $ insert s' 
				  PartialCompletion s -> do
					       let s' = drop (length pref) s
					       putStr (s'++ys)
					       debug ("partial completion: " ++ show pref ++ " to " ++ show s)
					       moveLeft (length ys)
					       loop $ insert s'
				  NoCompletion -> do 
						  debug ("No completion for prefix " ++ show pref)
				                  -- FIXME: beep?
						  commandLoop st 
				  AmbiguousCompletion xs -> 
				      do
				      debug ("Ambiguous completion for prefix " ++ show pref)
				      -- FIXME: allow C-d and/or double tab and/or asking to display all
				      commandLoop st
		    EndOfFile | null xs && null ys -> return st{ gotEOF = True }
		    Undo -> 
			do
			-- FIXME: implement
			debug "UNDO"
			commandLoop st
		    _ -> commandLoop st
	   where loop = commandLoop . modifyChars st
		 loopHistory cf hf = commandLoop $ modifyChars (modifyHistoryState st hf) cf

-- NOTE: hugs needs the hGetEcho / hSetEcho calls to be removed
withNoBuffOrEcho :: IO a -> IO a
withNoBuffOrEcho m = 
    do
    oldInBuf <- hGetBuffering stdin
    oldOutBuf <- hGetBuffering stdout
    oldEcho <- hGetEcho stdout
    hSetBuffering stdin NoBuffering
    hSetBuffering stdout NoBuffering
    hSetEcho stdout False
    m `finally` restore oldInBuf oldOutBuf oldEcho
    where restore oldInBuf oldOutBuf oldEcho =
	      do hSetBuffering stdin oldInBuf
		 hSetBuffering stdout oldOutBuf
		 hSetEcho stdout oldEcho

-- FIXME: restore terminal settings if interrupted
readline :: String -> IO (Maybe String)	    
readline prompt =
    do hPutStr stdout prompt
       hFlush stdout
       st <- initState
       st' <- withNoBuffOrEcho (commandLoop st)
       if gotEOF st' then
	  return Nothing 
	 else
          return $ Just $ toList $ chars st'
