#!/usr/bin/env runhaskell

{-# LANGUAGE ViewPatterns, LambdaCase #-}

import Test.QuickCheck
import System.IO.Unsafe
import Data.IORef
import Control.Monad
import System.Exit
import System.Posix.Process

prop_addDigits max ((`rem` max) -> a) ((`rem` max) -> b) = a >= 0 && b >= 0 && a <= max && b <= max ==> a' + b' == leleka ((+), "die Summe", "+") a' b'
    where (a', b') = (a + 2, b + 2)


prop_substDigits max ((`rem` max) -> a) ((`rem` max) -> b) = a >= 0 && b >= 0 && a <= max && b <= max ==> a' - b' == leleka ((-), "die Differenz", "-") a' b'
    where (a'', b'') = if a >= b then (a, b) else (b, a)
          (a', b') = (a'' + 3, b'' + 3)


prop_multDigits max ((`rem` max) -> a) ((`rem` max) -> b) = a >= 0 && b >= 0
                                                         && a <= max && b <= max
               ==> a' * b' == leleka ((*), "das Produkt", "*") a' b'
    where (a', b') = (a + 1, b + 1)


leleka :: (Int -> Int -> Int, String, String) -> Int -> Int -> Int
leleka (calc, job, op) a b = unsafePerformIO $ do
    c <- incCounter
    when (c > 0 && 0 == c `rem` 5) (putStrLn $ "(du hast jetzt " ++ show c ++ " gemacht)")
    putStrLn $ "Was ist " ++ job ++ " von " ++ show a ++ " und " ++ show b ++ " ?"
    getLine >>= correct 1 q (== a `calc` b)
  where q = putStrLn $ "Was ist " ++ show a ++ " " ++ op ++ " " ++ show b ++ " ?"

correct :: Int -> IO () -> (Int -> Bool) -> String -> IO Int
correct n q t "" = do putStrLn "Beenden? (Wenn nicht, die Zahl eingeben.)"
                      str <- getLine
                      if zahl str
                        then sicher n (read str) t q
                        else exitImmediately ExitSuccess >> return 0
correct n q t a | zahl a = sicher n (read a) t q
correct n q t x = do putStrLn $ "Das ist keine Zahl: \"" ++ x ++ "\""
                     --putStrLn $ "Was ist " ++ show a ++ " " ++ op ++ " " ++ show b ++ " ?"
                     q
                     getLine >>= correct n q t

sicher :: Int -> Int -> (Int -> Bool) -> IO () -> IO Int
sicher 0 antw t q = return antw
sicher n antw t q = if t antw
                      then return antw
                      else do putStrLn $ "Bist du sicher? Probier's nochmal:"
                              getLine >>= correct (n - 1) q t
zahl x = not (null x) && all (`elem` ['0'..'9']) x

prop_plusMinusDigits pl a b = if pl
                               then prop_addDigits 15 a b
                               else prop_substDigits 10 a b


prop_hunderterFeld :: Int -> Property
prop_hunderterFeld n = n > 0 ==> unsafePerformIO (lelekaFeld n') == n'
    where n' = n `rem` 101


lelekaFeld :: Int -> IO Int
lelekaFeld i = do
    putStrLn ""
    putStrLn $ "Welche Zahl im Hunderterfeld ist das?"
    putStrLn ""
    break $ mixed
    getLine >>= correct 1 q (== i)
  where q = putStrLn $ "Für welche Zahl steht '#'?"
        stars = repeat '*'
        mixed = take (i - 1) stars ++ '#' : take (100 - i) stars
        break "" = return ()
        break s = do putStrLn $ take 10 s
                     break $ drop 10 s

counter :: IORef Int
counter = unsafePerformIO $ newIORef (-1)

incCounter :: IO Int
incCounter = modifyIORef counter succ >> readIORef counter

main = do putStrLn "Plus, Minus oder Malaufgaben? Oder 100erfeld?"
          getLine >>= \case
            "+" -> quickCheck $ prop_addDigits 16
            "-" -> quickCheck $ prop_substDigits 11
            "+-" -> quickCheck prop_plusMinusDigits
            "*" -> quickCheck $ prop_multDigits 5
            "100" -> quickCheck $ prop_hunderterFeld
            _ -> putStrLn "Antworte mit '+', '-' oder '*'." >> main




data Verbo = Regular String
           | Irregular String String String

data Substantivo = Normal String
                 | SingOnly String

verbos = [ Irregular    "go"    "went"  "gone"
         , Irregular    "eat"   "ate"   "eaten"
         , Irregular     "sleep"   "slept"   "slept"
         , Irregular     "hide"   "hid"   "hidden"
         , Irregular     "do"   "did"   "done"
         , Irregular     "take"   "took"   "taken"
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         , Irregular     ""   ""   ""
         ]
