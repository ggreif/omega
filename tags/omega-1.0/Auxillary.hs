-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Thu Mar  3 11:15:06 Pacific Standard Time 2005
-- Omega Interpreter: version 1.0

module Auxillary where


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

maybeM :: Monad m => m(Maybe a) -> (a -> m b) -> (m b) -> m b
maybeM mma f mb = do { x <- mma; case x of { Nothing -> mb ; Just x -> f x }}

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
-- Display Info  (maps objects tagged with Integer to Strings)

class Display t where
  disp :: DispInfo -> t -> (DispInfo,String)
  
newtype DispInfo = DI ([(Integer,String)],[String])
initDI = DI([],makeNames "abcdefghijklmnopqrstuvwxyz")

instance Display Integer where
  disp d n = (d,show n)

-- We define a function "makeNames" which can be used to generate
-- an infinite list of distinct names based on some list of initial Chars
-- makeNames "ab" = ["a","b","a1","b1","a2","b2", ...]

makeNames source = g 0 (map (:[]) source)  -- "abc" --> ["a","b","c"]
   where g n x = map (h n) x ++ g (n+1) x
         h 0 s = s
         h n s = s++show n

dispL ::(DispInfo -> a -> (DispInfo,String)) -> DispInfo -> [a] -> String -> (DispInfo,String)
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

  
useDisplay :: Integer -> (String -> String) -> DispInfo -> (DispInfo,String)
useDisplay uniq newname (info@(DI(xs,n:ns))) = 
  case lookup uniq xs of
    Just s -> (info,s)
    Nothing -> (DI((uniq,name):xs,ns),name)
  where name = newname n

mergeDisp :: DispInfo -> DispInfo -> DispInfo
mergeDisp (DI(map1,src1)) (DI(map2,src2)) = DI(map3,src3)
  where src3 = if length map1 > length map2 then src1 else src2
        map3 = map2++map2

instance Show DispInfo where
  show (DI(xs,_)) = show xs
