-- Time-stamp: <2010-03-10 17:33:14 cklin>

module Common where

import Control.Monad (liftM)
import Data.List ((\\), nub, nubBy)
import Data.Map (Map, findWithDefault, fromList, toList)

type Endo a = a -> a

bug :: String -> a
bug msg = error ("BUG: " ++ msg)

same :: Eq a => [a] -> Bool
same [] = True
same xs = and (zipWith (==) (tail xs) xs)

unique :: [a] -> Maybe a
unique [x] = Just x
unique _ = Nothing

unions :: Eq a => [[a]] -> [a]
unions = nub . concat

unionMap :: Eq b => (a -> [b]) -> [a] -> [b]
unionMap f = unions . map f

map1st :: (a -> b) -> [(a, c)] -> [(b, c)]
map1st f = map (\(u, v) -> (f u, v))

nub1st :: Eq a => Endo [(a, b)]
nub1st = nubBy (\(a, _) (c, _) -> a == c)

overlaps :: Ord a => [a] -> [a] -> Bool
overlaps = any . flip elem

subset :: Eq a => [a] -> [a] -> Bool
subset ux wx = null (ux \\ wx)

lookupX :: Ord k => k -> Map k a -> a
lookupX = findWithDefault (bug "Missing key in lookupX")

lookupZ :: Ord k => k -> Map k k -> k
lookupZ k = findWithDefault k k

-- This is a version of Map.fromList that checks that there are no
-- duplicate keys in the input association list.

toMap :: (Ord k, Show k) => [(k, a)] -> Map k a
toMap assoc =
    let keys = map fst assoc
        dups = nub (keys \\ nub keys)
    in if null dups then fromList assoc
       else bug ("Duplicate keys " ++ show dups)

