#!/usr/bin/env runhaskell

import Test.QuickCheck
import System.IO.Unsafe
import System.Exit
import System.Posix.Process

prop_addDigits max a b = a >= 0 && b >= 0 && a <= max && b <= max ==> a + b == leleka a b

leleka :: Int -> Int -> Int
leleka a b = unsafePerformIO $ do
    putStrLn $ "Was ist die Summe von " ++ show a ++ " und " ++ show b ++ " ?"
    str <- getLine
    if null str
      then exitImmediately ExitSuccess >> return 0
      else return $ read str


main = quickCheck $ prop_addDigits 15