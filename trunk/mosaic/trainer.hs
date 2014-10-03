#!/usr/bin/env runhaskell

{-# LANGUAGE ViewPatterns #-}

import Test.QuickCheck
import System.IO.Unsafe
import System.Exit
import System.Posix.Process

prop_addDigits max ((`rem` max) -> a) ((`rem` max) -> b) = a >= 0 && b >= 0 && a <= max && b <= max ==> a + b == leleka a b

leleka :: Int -> Int -> Int
leleka a b = unsafePerformIO $ do
    putStrLn $ "Was ist die Summe von " ++ show a ++ " und " ++ show b ++ " ?"
    str <- getLine
    correct str
  where correct "" = do putStrLn "Beenden? (Wenn nicht, die Zahl eingeben.)"
  		     	str <- getLine
			if zahl str
			  then return $ read str
			  else exitImmediately ExitSuccess >> return 0
	correct a | zahl a = return $ read a
	correct x = do putStrLn $ "Das ist keine Zahl: " ++ x
		       putStrLn $ "Was ist " ++ show a ++ " + " ++ show b ++ " ?"
		       getLine >>= correct
	zahl x = not (null x) && all (`elem` ['0'..'9']) x

main = quickCheck $ prop_addDigits 15