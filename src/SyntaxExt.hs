
module SyntaxExt where

import Auxillary
import ParserAll  -- This for defining parsers
-- To import ParserAll you must define CommentDef.hs and TokenDef.hs
-- These should be in the same directory as this file.
import Char(isLower)

import qualified Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.HughesPJ(Doc,text,int,(<>),(<+>),($$),($+$),render)

data SynExt t -- Syntax Extension
  = Ox               -- no extension
  | Lx (String,t,t)  -- list extension like [a,b,c]i
  | Nx (String,t,t)  -- number extension like 4i
  | Px (String,t)    -- pair extension like (a,b)i
  | Rx (String,t,t)  -- record extension like {a=t,b=s}r

data Extension t
  = Listx [t] (Maybe t) String        --  [x,y ; zs]i
  | Numx Int (Maybe t) String         --  4i   #(2+x)i
  | Pairx [t] String                  --  (a,b,c)i
  | Recordx [(t,t)] (Maybe t) String  --  {x=t,y=s ; zs}i

-------------------------------------------------------------
-- Show instances

instance Show a => Show (SynExt a) where
  show Ox = "Ox"
  show (Lx(k,a,b)) = "Lx("++k++","++show a++","++show b++")"
  show (Nx(k,a,b)) = "Nx("++k++","++show a++","++show b++")"
  show (Px(k,a)) = "Px("++k++","++show a++")"
  show (Rx(k,a,b)) = "Rx("++k++","++show a++","++show b++")"

instance Show x => Show(Extension x) where
  show (Listx ts Nothing tag) = plist "[" ts "," ("]"++tag)
  show (Listx ts (Just t) tag) = plist "[" ts "," "; " ++ show t ++"]"++tag
  show (Numx n Nothing tag) = show n++tag
  show (Numx n (Just t) tag) = "("++show n++"+"++show t++")"++tag
  show (Pairx ts tag) = "("++ help ts++ ")"++tag
    where help [] = ""
          help [x] = show x
          help (x:xs) = show x++","++help xs
  show (Recordx ts Nothing tag) = plistf f "{" ts "," ("}"++tag)
    where f (x,y) = show x++"="++show y

extKey :: Extension a -> String
extKey ((Listx xs _ s)) = s
extKey ((Recordx xs _ s)) = s
extKey ((Numx n _ s)) = s
extKey ((Pairx xs s)) = s

extName :: Extension a -> String
extName ((Listx xs _ s)) = "List"
extName ((Recordx xs _ s)) = "Record"
extName ((Numx n _ s)) = "Nat"
extName ((Pairx xs s)) = "Pair"

----------------------------------------------------
-- Creating formatted documents

ppExt :: (a -> Doc) -> Extension a -> Doc
ppExt f((Listx xs (Just x) s)) = PP.sep ((text "["):(map f xs)++[text ";",f x,text ("]"++s)])
ppExt f((Listx xs Nothing s)) = PP.sep ((text "["):(map f xs)++[text ("]"++s)])
ppExt f((Numx n (Just x) s)) = PP.hcat [text "(",PP.int n,text "+",f x,text (")"++s)]
ppExt f((Numx n Nothing s)) = PP.hcat [PP.int n,text s]
ppExt f((Pairx xs s)) = text "(" <> PP.hcat(PP.punctuate PP.comma (map f xs)) <> text (")"++s)
ppExt f((Recordx xs (Just x) s)) = text "{" <> PP.hcat(PP.punctuate PP.comma (map g xs)) <> PP.semi <> f x <> text ("}"++s)
  where g (x,y) = f x <> text "=" <> f y
ppExt f((Recordx xs Nothing s)) = text "{" <> PP.hcat(PP.punctuate PP.comma (map g xs)) <> text ("}"++s)
  where g (x,y) = f x <> text "=" <> f y

-------------------------------------------------------
-- map and fold-like operations

extList :: Extension a -> [a]
extList ((Listx xs (Just x) _)) = (x:xs)
extList ((Listx xs Nothing _)) = xs
extList ((Recordx xs (Just x) _)) = (x: flat2 xs)
extList ((Recordx xs Nothing _)) = flat2 xs
extList ((Numx n (Just x) _)) = [x]
extList ((Numx n Nothing _)) = []
extList ((Pairx xs _)) = xs

instance Eq t => Eq (Extension t) where
 (Listx ts1 (Just t1) s1) == (Listx xs1 (Just x1) s2) = s1==s2 && (t1:ts1)==(x1:xs1)
 (Listx ts1 Nothing s1) == (Listx xs1 Nothing s2) = s1==s2 && (ts1)==(xs1)
 (Numx n (Just t1) s1) == (Numx m (Just x1) s2) = s1==s2 && t1==x1 && n==m
 (Numx n Nothing s1) == (Numx m Nothing s2) = s1==s2 && n==m
 (Pairx xs s) == (Pairx ys t) = xs==ys && s==t
 (Recordx ts1 (Just t1) s1) == (Recordx xs1 (Just x1) s2) = s1==s2 && t1==x1 && ts1==xs1
 (Recordx ts1 Nothing s1) == (Recordx xs1 Nothing s2) = s1==s2 && (ts1)==(xs1)
 _ == _ = False

extM :: Monad a => (b -> a c) -> Extension b -> a (Extension c)
extM f (Listx xs (Just x) s) = do { ys <- mapM f  xs; y<- f  x;return((Listx ys (Just y) s))}
extM f (Listx xs Nothing s) = do { ys <- mapM f  xs; return((Listx ys Nothing s))}
extM f (Numx n (Just x) s) = do { y<- f  x; return((Numx n (Just y) s))}
extM f (Numx n Nothing s) = return((Numx n Nothing s))
extM f (Pairx xs s) =  do { ys <- mapM f  xs; return((Pairx ys s))}
extM f (Recordx xs (Just x) s) = do { ys <- mapM g  xs; y<- f  x;return((Recordx ys (Just y) s))}
  where g (x,y) = do { a <- f x; b <- f y; return(a,b) }
extM f (Recordx xs Nothing s) = do { ys <- mapM g  xs; return((Recordx ys Nothing s))}
 where g (x,y) = do { a <- f x; b <- f y; return(a,b) }

threadL f [] n = return([],n)
threadL f (x:xs) n =
  do { (x',n1) <- f x n
     ; (xs',n2) <- threadL f xs n1
     ; return(x' : xs', n2)}

threadPair f (x,y) n = do { (a,n1) <- f x n; (b,n2) <- f y n1; return((a,b),n2)}

extThread :: Monad m => (b -> c -> m(d,c)) -> c -> Extension b -> m(Extension d,c)
extThread f n (Listx xs (Just x) s) =
  do { (ys,n1) <- threadL f xs n; (y,n2) <- f x n1; return(Listx ys (Just y) s,n2)}
extThread f n (Listx xs Nothing s) =
  do { (ys,n1) <- threadL f xs n; return(Listx ys Nothing s,n1)}
extThread f n (Numx m (Just x) s) = do { (y,n1) <- f x n; return(Numx m (Just y) s,n1)}
extThread f n (Numx m Nothing s) = return(Numx m Nothing s,n)
extThread f n (Pairx xs s) =  do { (ys,n1) <- threadL f xs n; return(Pairx ys s,n1)}
extThread f n (Recordx xs (Just x) s) =
  do { (ys,n1) <- threadL (threadPair f) xs n; (y,n2) <- f x n1; return(Recordx ys (Just y) s,n2)}
extThread f n (Recordx xs Nothing s) =
  do { (ys,n1) <- threadL (threadPair f) xs n; return(Recordx ys Nothing s,n1)}

cross f (x,y) = (f x,f y)

instance Functor Extension where
  fmap f (Listx xs (Just x) s) = (Listx (map f xs) (Just(f x)) s)
  fmap f (Listx xs Nothing s) = (Listx (map f xs) Nothing s)
  fmap f (Numx n (Just x) s) = (Numx n (Just (f x)) s)
  fmap f (Numx n Nothing s) = (Numx n Nothing s)
  fmap f (Pairx xs s) =  (Pairx (map f xs) s)
  fmap f (Recordx xs (Just x) s) = (Recordx (map (cross f) xs) (Just(f x)) s)
  fmap f (Recordx xs Nothing s) = (Recordx (map (cross f) xs) Nothing s)

--------------------------------------------------------
-- Other primitive operations like selection and equality

-- Equal if the same kind and the same key,
instance Eq a => Eq (SynExt a) where
  Ox == Ox = True
  (Lx(k1,_,_)) == (Lx(k2,_,_)) = k1==k2
  (Nx(k1,_,_)) == (Nx(k2,_,_)) = k1==k2
  (Px(k1,_)) == (Px(k2,_)) = k1==k2
  (Rx(k1,_,_)) == (Rx(k2,_,_)) = k1==k2
  _ == _ = False

synKey Ox = ""
synKey (Lx (s,_,_)) = s
synKey (Nx (s,_,_)) = s
synKey (Px (s,_)) = s
synKey (Rx (s,_,_)) = s

synName Ox = ""
synName (Lx (s,_,_)) = "List"
synName (Nx (s,_,_)) = "Nat"
synName (Px (s,_)) = "Pair"
synName (Rx (s,_,_)) = "Record"


-- Both the name and the type match. Different types (i.e. List,Nat,Pair)
-- can use the same name.
matchExt loc (Listx _ _ s) (Lx(t,_,_)) | s==t = return True
matchExt loc (Numx _ _ s) (Nx(t,_,_)) | s==t = return True
matchExt loc (Pairx _ s) (Px(t,_)) | s==t = return True
matchExt loc (Recordx _ _ s) (Rx(t,_,_)) | s==t = return True
matchExt loc (Listx _ _ "") _ = return False
matchExt loc (Numx _ _ "") _ = return False
matchExt loc (Pairx _ "") _ = return False
matchExt loc (Recordx _ _ "") _ = return False
matchExt loc _ _ = return False

----------------------------------------------------------
-- Building such objects in an abstract manner

build (cons,nil,succ,zero,pair,rcons,rnil) x =
  case x of
   (Listx xs (Just x) _) -> foldr cons x xs
   (Listx xs Nothing _) -> foldr cons nil xs
   (Numx n (Just x) _) -> buildNat x succ n
   (Numx n Nothing _) -> buildNat zero succ n
   (Pairx xs _) -> buildTuple pair xs
   (Recordx xs (Just x) _) -> foldr (uncurry rcons) x xs
   (Recordx xs Nothing _) -> foldr (uncurry rcons) rnil xs

findM:: Monad m => String -> (a -> m Bool) -> [a] -> m a
findM mes p [] = fail mes
findM mes p (x:xs) =
  do { b <- p x
     ; if b then return x else findM mes p xs}

buildExt :: (Show c,Show b,Monad m) => String -> (b -> c,b -> c -> c,b -> c -> c -> c,b -> c -> c -> c -> c) ->
                      Extension c -> [SynExt b] -> m c
buildExt loc (lift0,lift1,lift2,lift3) x ys =
  do { y <- findM ("\nCan't find a "++extName x++" syntax extension called: "++
                   extKey x++", at "++loc++"\n  "++show x++"\n  "++show ys)
                  (matchExt loc x) ys
     ; case (x,y) of
        (Listx xs (Just x) _,Lx(tag,nil,cons)) -> return(foldr (lift2 cons) x xs)
        (Listx xs Nothing  _,Lx(tag,nil,cons)) -> return(foldr (lift2 cons) (lift0 nil) xs)
        (Recordx xs (Just x) _,Rx(tag,nil,cons)) -> return(foldr (uncurry(lift3 cons)) x xs)
        (Recordx xs Nothing  _,Rx(tag,nil,cons)) -> return(foldr (uncurry(lift3 cons)) (lift0 nil) xs)
        (Numx n (Just x) _,Nx(tag,zero,succ)) -> return(buildNat x (lift1 succ) n)
        (Numx n Nothing  _,Nx(tag,zero,succ)) -> return(buildNat (lift0 zero) (lift1 succ) n)
        (Pairx xs _,Px(tag,pair)) -> return(buildTuple (lift2 pair) xs)
        _ -> fail ("\nSyntax extension: "++extKey x++" doesn't match use, at "++loc)}

listx = Lx("","[]",":")
natx = Nx("n","Z","S")
pairx = Px("","(,)")
recordx = Rx("","Rnil","Rcons")

buildNat :: Num a => b -> (b -> b) -> a -> b
buildNat z s 0 = z
buildNat z s n = s(buildNat z s (n-1))

buildTuple pair [] = error "No empty tuples: ()"
buildTuple pair [p] = p
buildTuple pair [x,y] = pair x y
buildTuple pair (x:xs) = pair x (buildTuple pair xs)

flat2 [] = []
flat2 ((a,b):xs) = a : b : flat2 xs

-----------------------------------------------------------
-- Parsers for syntactic Extensions
--  #"abc"   #[x,y ; zs]i   #4i   #(2+x)i    #(a,b,c)i #{a:Int,b:String; r}i

semiTailSeq left right elem tail buildf =
  do { lexeme left
     ; xs <- sepBy elem comma
     ; x <- (do { semi; y <- tail; return(Just y)}) <|>
            (return Nothing)
     ; right  -- No lexeme here because the tag must follow immediately
     ; tag <- many (lower <|> char '\'')
     ; return(buildf xs x tag)}

extP :: Parser a -> Parser (Extension a)
extP p = try(lexeme(listP p <|> parensP p <|> recP p))
  where listP p = semiTailSeq (char '[') (char ']') p p Listx
        recP p = semiTailSeq (char '{') (char '}') pair p Recordx
          where pair = do { x <- p; symbol "="; y <- p; return(x,y)}

parensP p =
   do { f <- try(incr p) <|> try(seqX p)
      ; tag <- many lower
      ; return(f tag)}
incr p =
   do { lexeme (char '(')
      ; n <- lexeme natNoSpace
      ; symbol "+"; x <- p
      ; char ')'
      ; return(Numx n (Just x))}
seqX p =
  do { lexeme (char '(')
     ; xs <- sepBy p comma
     ; char ')'
     ; return(Pairx xs)}

natP :: Parser (Extension a)
natP = try $ lexeme $
       (do{ satisfy ('#'==); n <- natNoSpace; return(Numx n Nothing "n")}) <|>
       (do{ n <- natNoSpace; tag <- many lower; return(Numx n Nothing tag)})

