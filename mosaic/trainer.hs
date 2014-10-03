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
    getLine >>= correct 1
  where correct :: Int -> String -> IO Int
        correct n "" = do putStrLn "Beenden? (Wenn nicht, die Zahl eingeben.)"
                          str <- getLine
                          if zahl str
                            then sicher n (read str)
                            else exitImmediately ExitSuccess >> return 0
        correct n a | zahl a = sicher n (read a)
        correct n x = do putStrLn $ "Das ist keine Zahl: " ++ x
                         putStrLn $ "Was ist " ++ show a ++ " + " ++ show b ++ " ?"
                         getLine >>= correct n
        sicher :: Int -> Int -> IO Int
        sicher 0 antw = return antw
        sicher n antw = if antw == a + b
                           then return antw
                           else do putStrLn $ "Bist du sicher? Probier's nochmal:"
                                   getLine >>= correct (n - 1)
        zahl x = not (null x) && all (`elem` ['0'..'9']) x

main = quickCheck $ prop_addDigits 15
