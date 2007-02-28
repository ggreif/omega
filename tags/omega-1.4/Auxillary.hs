-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Tue Feb 27 21:04:24 Pacific Standard Time 2007
-- Omega Interpreter: version 1.4

module Auxillary where

import Char(isAlpha)
import List(find,union)


whenM :: Monad m => m Bool -> m b -> [Char] -> m b
whenM test x s = do { b <- test; if b then x else error s}

ifM :: Monad m => m Bool -> m b -> m b -> m b
ifM test x y = do { b <- test; if b then x else y }

anyM :: Monad m => (b -> m Bool) -> [b] -> m Bool
anyM p xs = do { bs <- mapM p xs; return(or bs) }


allM :: Monad m => (b -> m Bool) -> [b] -> m Bool
allM p xs = do { bs <- mapM p xs; return(and bs) }


orM :: Monad m => m Bool -> m Bool -> m Bool
orM x y = do { a <- x; b <- y; return (a || b) }

foldrM :: Monad m => (a -> b -> m b) -> b -> [a] -> m b
foldrM acc base [] = return base
foldrM acc base (x:xs) = do { b <- acc x base; foldrM acc b xs}

foldlM :: Monad m => (a -> b -> m b) -> b -> [a] -> m b
foldlM acc base [] = return base
foldlM acc base (x:xs) = do { b <- foldrM acc base xs; acc x b; }

maybeM :: Monad m => m(Maybe a) -> (a -> m b) -> (m b) -> m b
maybeM mma f mb = do { x <- mma; case x of { Nothing -> mb ; Just x -> f x }}

eitherM comp f g = do { x <- comp; case x of {Left x -> f x; Right x -> g x}}

{-- Already in Monad
filterM :: Monad m => (a -> m Bool) -> [a] -> m[a]
filterM p [] = return []
filterM p (x:xs) =
   ifM (p x) (do { ys <- filterM p xs; return (x:ys)}) (filterM p xs)
-}

splitM ::  Monad m => (a -> m Bool) -> [a] -> m([a],[a])
splitM p xs = foldrM acc ([],[]) xs
  where acc x (ys,zs) = ifM (p x) (return(x:ys,zs)) (return(ys,x:zs))

--------------------------------------------------------

plist :: Show a => String -> [a] -> String -> String -> String
plist open xs sep close = open ++ help xs ++ close
  where help [] = ""
        help [x] = show x
        help (x:xs) = show x ++ sep ++ help xs

plistf :: (a -> String) -> String -> [a] -> String -> String -> String
plistf f open xs sep close = open ++ help xs ++ close
  where help [] = ""
        help [x] = f x
        help (x:xs) = f x ++ sep ++ help xs


extend f v x y = if x==y then v else f y

extendM :: (Eq a,Monad m) => (a -> m b) -> b -> a -> a -> m b
extendM f v x y = if x==y then return v else f y

extendL :: Eq a => (a -> b) -> [(a,b)] -> a -> b
extendL f [] y = f y
extendL f ((x,v):xs) y = if x==y then v else extendL f xs y

elemBy :: (a -> a -> Bool) -> a -> [a] -> Bool
elemBy p x xs = any (p x) xs

prefix [] xs = True
prefix (x:xs) (y:ys) | x==y = prefix xs ys
prefix _ _ = False

backspace [] ans = reverse ans
backspace (x:xs) []  | x == '\BS' = backspace xs []
backspace (x:xs) ans | x == '\BS' = backspace xs (tail ans)
                     | True       = backspace xs (x:ans)

---------------------------------------------------------------
-- Locations

data Loc = SrcLoc Int Int | Z
loc0 = Z

instance Show Loc where
  show (SrcLoc x y) = "line: "++(show x)++" column: "++(show y)
  show Z = "unknown location"

showLocLine (SrcLoc x y) = show x
showLocLine Z = "unknown line"

report :: Monad m => Loc -> String -> m a
report Z s = fail ("\n"++s)
report loc s = fail ("\nError near "++(show loc)++"\n"++s)

------------------------------------------------------
-- Display Info  (maps objects tagged with `a` to Strings)

class (Show a,Eq a) => Display t a where
  disp :: DispInfo a -> t -> (DispInfo a,String)

newtype DispInfo a = DI ([(a,String)],[String],[String])
--                       map          bad      name-supply

------------------------------------------------------

initDI = DI([],[],makeNames "abcdefghijklmnopqrstuvwxyz")

intDI:: DispInfo Int
intDI = initDI

newDI xs = DI(xs,map snd xs,makeNames "abcdefghijklmnopqrstuvwxyz")

-- We define a function "makeNames" which can be used to generate
-- an infinite list of distinct names based on some list of initial Chars
-- makeNames "ab" = ["a","b","a1","b1","a2","b2", ...]

makeNames source = g 0 (map (:[]) source)  -- "abc" --> ["a","b","c"]
   where g n x = map (h n) x ++ g (n+1) x
         h 0 s = s
         h n s = s++show n

--dispL ::(DispInfo -> a -> (DispInfo,String)) -> DispInfo -> [a] -> String -> (DispInfo,String)
dispL f xs [] sep = (xs,"")
dispL f xs [m] sep = f xs m
dispL f xs (m:ms) sep = (zs,a++sep++b)
  where (ys,a) = f xs m
        (zs,b) = dispL f ys ms sep

disp2 xs1 (x,y) = (xs3,sx,sy)
  where (xs2,sx) = disp xs1 x
        (xs3,sy) = disp xs2 y

disp3 xs1 (x,y,z) = (xs4,sx,sy,sz)
  where (xs2,sx) = disp xs1 x
        (xs3,sy) = disp xs2 y
        (xs4,sz) = disp xs3 z

disp4 xs0 (w,x,y,z) = (xs4,sw,sx,sy,sz)
  where (xs1,sw) = disp xs0 w
        (xs2,sx) = disp xs1 x
        (xs3,sy) = disp xs2 y
        (xs4,sz) = disp xs3 z

disp5 xs0 (w,x,y,z,a) = (xs5,sw,sx,sy,sz,sa)
  where (xs1,sw) = disp xs0 w
        (xs2,sx) = disp xs1 x
        (xs3,sy) = disp xs2 y
        (xs4,sz) = disp xs3 z
        (xs5,sa) = disp xs4 a


useDisplay :: Eq a => (String -> String) -> DispInfo a -> a -> (DispInfo a,String)
useDisplay newnamef (info@(DI(xs,bad,supply))) uniq =
  case lookup uniq xs of
    Just y -> (info,y)
    Nothing -> let (m,supply2) = next bad supply
                   name = newnamef m
               in (DI((uniq,name):xs,bad,supply2),name)

next bad (x:xs) = if notIn bad x then (x,xs) else next bad xs
  where notIn [] x = True
        notIn (y:ys) x = if (root x)==(root y) then False else notIn ys x
        root (c:cs) | not(isAlpha c) = root cs
        root cs = cs

{-  SOME TESTS to turn into Unit Tests
d0 = newDI [(1::Int,"b"),(2,"c")]
ans = displays d1 [Ds "A",Df f 1, Df f 0, Df f 2, Df f 3, Df f 4,Df f 1,Ds "Z",Df f 3]

f::  DispInfo Int -> Int -> (DispInfo Int,String)
f = useDisplay (\ x -> x)
d1 :: DispInfo Int
d1 = newDI []
(d2,_) = tryDisplay 0 "a" 1 id d1
(d3,_) = tryDisplay 0 "b" 2 id d2
(d4,_) = tryDisplay 0 "a" 3 id d3
(d5,_) = tryDisplay 0 "x" 4 id d4
d6 = displays d5 [Ds "[",Df f 1,Df f 2,Df f 3, Df f 4,Df f 5,Ds "]"]
-}

-- Here we suggest a name "x" for a variable "uniq", if "uniq" isn't
-- already mapped to some other name. If it is still not mapped we
-- use "x" if it is still available, "x1", or "x2", or "x3" etc if
-- "x" is already in use.

tryDisplay n firstx x uniq newf (info@(DI(xs,bad,supply))) =
  case lookup uniq xs of
    Just y -> (info,y)
    Nothing -> case find alreadyInUse xs of
                Nothing -> (DI((uniq,name):xs,name:bad,supply),name)
                       where name = newf x
                Just _ -> tryDisplay (n+1) firstx (next firstx) uniq newf info
 where next x = x++show n
       alreadyInUse (a,nm) = nm== newf x



{-
mergeDisp :: DispInfo a -> DispInfo a -> DispInfo a
mergeDisp (DI(map1,bad1,src1)) (DI(map2,bad2,src2)) = DI(map3,bad3,src3)
  where src3 = if length map1 > length map2 then src1 else src2
        map3 = map1++map2
        bad3 = union bad1 bad2
-}


instance Show a => Show (DispInfo a) where
  show (DI(xs,bad,names)) = "(DI "++show xs++" "++show bad++" "++show(take 6 names)++")"

data DispElem a
  = forall x . (Display x a) =>  Dd x
  | Ds String
  | forall x . (Display x a) => Dn x
  | forall x . (Display x a) => Dl [x] String
  | forall x . (Display x a) => Dwrap Int String [x] String
  | forall x . Df (DispInfo a -> x -> (DispInfo a ,String)) x
  | forall x . Dlf (DispInfo a -> x -> (DispInfo a,String)) [x] String
  | forall x . Dlg (DispInfo a -> x -> (DispInfo a,String)) String [x] String String
  | Dr [DispElem a]

drI:: DispInfo z -> [DispElem z] -> DispElem z
drI _ xs = Dr xs


dlfI:: (DispInfo z -> x -> DispElem z) -> [x] -> String -> DispElem z
dlfI f xs sep = Dlf (\ d x -> displays d [f d x]) xs sep

displays :: DispInfo a -> [DispElem a] -> (DispInfo a,String)
displays d xs = help d (reverse xs) "" where
  help:: DispInfo a -> [DispElem a] -> String -> (DispInfo a,String)
  help d [] s = (d,s)
  help d ((Dr xs):ys) s = help d (reverse xs++ys) s
  help d (x:xs) s = help d2 xs (s2++s)
    where (d2,s2) =
             case x of
               Dd y -> disp d y
               Ds s -> (d,s)
               Dn y -> let (d2,s) = disp d y in (d2,s++"\n")
               Dl ys sep -> dispL disp d ys sep
               Dwrap max prefix xs sep -> wrap 0 n max n xs sep [prefix,"\n"] d
                  where n = length prefix
               Df f ys  -> f d ys
               Dlf f ys sep -> dispL f d ys sep
               Dlg f open [] sep close -> (d,"")
               Dlg f open ys sep close ->
                 let (d2,inner) = dispL f d ys sep
                 in (d2,open++inner++close)



-- displays d [dv "x" 123]  --->  "x = 1233"
dv s x = Dr [Ds ", ",Dd x,Ds (s++" = ")]

wrap count current max indent [] sep ans info = (info,concat (reverse ans))
wrap count current max indent (x:xs) sep ans info =
  case disp info x of
    (info2,str) -> let l = length str
                       s = length sep
                   in if (current+l <= max) || (count == 0)
                         then wrap (count + 1) (current + l + s) max indent xs sep (sep:str:ans) info2
                         else wrap 1 (l + indent) max indent xs sep
                                   ([sep,str,spaces indent,"\n"]++ans) info2
spaces n | n<= 0 = []
spaces n = ' ': spaces (n-1)

ns :: [Int]
ns = [1 .. 50]