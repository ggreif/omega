
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
  | Ix (String,Maybe(t,t),Maybe(t,t),Maybe t,Maybe(t,t),Maybe t)
  | Lx (String,t,t)  -- list extension like [a,b,c]i
  | Nx (String,t,t)  -- number extension like 4i
  | Px (String,t)    -- pair extension like (a,b)i
  | Rx (String,t,t)  -- record extension like {a=t,b=s}r
  | Tx (String,t)    -- Tick extension like (e+3)i
  
data Extension t
  = Listx [t] (Maybe t) String        --  [x,y ; zs]i
  | Numx Int (Maybe t) String         --  4i   #(2+x)i
  | Pairx [t] String                  --  (a,b,c)i
  | Recordx [(t,t)] (Maybe t) String  --  {x=t,y=s ; zs}i
  | Tickx Int t String                --  (e+3)i

-------------------------------------------------------------
-- Show instances

instance Show a => Show (SynExt a) where
  show Ox = "Ox"
  show (Ix(k,l,n,p,r,t)) = "Ix "++k++f "List" l++f "Nat" n++g "Pair" p++f "Record" r++g "Tick" t
     where f nm Nothing = ""
           f nm (Just(x,y)) = " "++nm++"["++show x++","++show y++"]"
           g nm Nothing = ""
           g nm (Just x) = " "++nm++"["++show x++"]"
  show (Lx(k,a,b)) = "Lx("++k++","++show a++","++show b++")"
  show (Nx(k,a,b)) = "Nx("++k++","++show a++","++show b++")"
  show (Px(k,a)) = "Px("++k++","++show a++")"
  show (Rx(k,a,b)) = "Rx("++k++","++show a++","++show b++")"
  show (Tx(k,a)) = "Tx("++k++","++show a++")"


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
  show (Recordx ts (Just ys) tag) =  plistf f "{" ts "," (";"++show ys++"}"++tag)
    where f (x,y) = show x++"="++show y 
  show (Tickx n t tag) = "("++show t++"`"++show n++")"++tag

extKey :: Extension a -> String
extKey ((Listx xs _ s)) = s
extKey ((Recordx xs _ s)) = s
extKey ((Numx n _ s)) = s
extKey ((Pairx xs s)) = s
extKey ((Tickx n x s)) = s


extName :: Extension a -> String
extName ((Listx xs _ s)) = "List"
extName ((Recordx xs _ s)) = "Record"
extName ((Numx n _ s)) = "Nat"
extName ((Pairx xs s)) = "Pair"
extName ((Tickx n _ s)) = "Tick"

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
ppExt f((Tickx n x s)) = PP.hcat [text "(",f x,text "`",PP.int n,text (")"++s)]


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
extList ((Tickx n x _)) = [x]

instance Eq t => Eq (Extension t) where
 (Listx ts1 (Just t1) s1) == (Listx xs1 (Just x1) s2) = s1==s2 && (t1:ts1)==(x1:xs1)
 (Listx ts1 Nothing s1) == (Listx xs1 Nothing s2) = s1==s2 && (ts1)==(xs1)
 (Numx n (Just t1) s1) == (Numx m (Just x1) s2) = s1==s2 && t1==x1 && n==m
 (Numx n Nothing s1) == (Numx m Nothing s2) = s1==s2 && n==m
 (Pairx xs s) == (Pairx ys t) = xs==ys && s==t
 (Recordx ts1 (Just t1) s1) == (Recordx xs1 (Just x1) s2) = s1==s2 && t1==x1 && ts1==xs1
 (Recordx ts1 Nothing s1) == (Recordx xs1 Nothing s2) = s1==s2 && (ts1)==(xs1)
 (Tickx n t1 s1) == (Tickx m x1 s2) = s1==s2 && t1==x1 && n==m
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
extM f (Tickx n x s) = do { y<- f  x; return((Tickx n y s))} 
 

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
extThread f n (Tickx m x s) = do { (y,n1) <- f x n; return(Tickx m y s,n1)}

cross f (x,y) = (f x,f y)

instance Functor Extension where
  fmap f (Listx xs (Just x) s) = (Listx (map f xs) (Just(f x)) s)
  fmap f (Listx xs Nothing s) = (Listx (map f xs) Nothing s)
  fmap f (Numx n (Just x) s) = (Numx n (Just (f x)) s)
  fmap f (Numx n Nothing s) = (Numx n Nothing s)
  fmap f (Pairx xs s) =  (Pairx (map f xs) s)
  fmap f (Recordx xs (Just x) s) = (Recordx (map (cross f) xs) (Just(f x)) s)
  fmap f (Recordx xs Nothing s) = (Recordx (map (cross f) xs) Nothing s)
  fmap f (Tickx n x s) = (Tickx n (f x) s)

--------------------------------------------------------
-- Other primitive operations like selection and equality

-- Equal if the same kind and the same key,
instance Eq a => Eq (SynExt a) where
  Ox == Ox = True
  (Lx(k1,_,_)) == (Lx(k2,_,_)) = k1==k2
  (Nx(k1,_,_)) == (Nx(k2,_,_)) = k1==k2
  (Px(k1,_)) == (Px(k2,_)) = k1==k2
  (Rx(k1,_,_)) == (Rx(k2,_,_)) = k1==k2
  (Ix(k1,_,_,_,_,_)) == (Ix(k2,_,_,_,_,_)) = k1==k2
  (Tx(k1,_)) == (Tx(k2,_)) = k1==k2
  _ == _ = False

synKey Ox = ""
synKey (Lx (s,_,_)) = s
synKey (Nx (s,_,_)) = s
synKey (Px (s,_)) = s
synKey (Rx (s,_,_)) = s
synKey (Tx (s,_)) = s
synKey (Ix (s,_,_,_,_,_)) = s


synName Ox = ""
synName (Lx (s,_,_)) = "List"
synName (Nx (s,_,_)) = "Nat"
synName (Px (s,_)) = "Pair"
synName (Rx (s,_,_)) = "Record"
synName (Tx (s,_)) = "Tick"
synName (Ix (s,Just _,_,_,_,_)) = "List"
synName (Ix (s,_,Just _,_,_,_)) = "Nat"
synName (Ix (s,_,_,Just _,_,_)) = "Pair"
synName (Ix (s,_,_,_,Just _,_)) = "Record"
synName (Ix (s,_,_,_,_,Just _)) = "Tick"


-- Both the name and the type match. Different types (i.e. List,Nat,Pair)
-- can use the same name.
matchExt loc (Listx _ _ s) (Lx(t,_,_)) | s==t = return True
matchExt loc (Listx _ _ s) (Ix(t,Just _,_,_,_,_)) | s==t = return True
matchExt loc (Numx _ _ s)  (Nx(t,_,_)) | s==t = return True
matchExt loc (Numx _ _ s)  (Ix(t,_,Just _,_,_,_)) | s==t = return True
matchExt loc (Pairx _ s)   (Px(t,_)) | s==t = return True
matchExt loc (Pairx _ s)   (Ix(t,_,_,Just _,_,_)) | s==t = return True
matchExt loc (Recordx _ _ s)  (Rx(t,_,_)) | s==t = return True
matchExt loc (Recordx _ _ s)  (Ix(t,_,_,_,Just _,_)) | s==t = return True
matchExt loc (Tickx _ _ s)    (Tx(t,_)) | s==t = return True
matchExt loc (Tickx _ _ s)    (Ix(t,_,_,_,_,Just _)) | s==t = return True
matchExt loc (Listx _ _ "") _ = return False
matchExt loc (Numx _ _ "") _ = return False
matchExt loc (Pairx _ "") _ = return False
matchExt loc (Recordx _ _ "") _ = return False
matchExt loc (Tickx _ _ "") _ = return False
matchExt loc _ _ = return False

----------------------------------------------------------
-- Building such objects in an abstract manner

build (cons,nil,succ,zero,pair,rcons,rnil,tick) x =
  case x of
   (Listx xs (Just x) _) -> foldr cons x xs
   (Listx xs Nothing _) -> foldr cons nil xs
   (Numx n (Just x) _) -> buildNat x succ n
   (Numx n Nothing _) -> buildNat zero succ n
   (Pairx xs _) -> buildTuple pair xs
   (Recordx xs (Just x) _) -> foldr (uncurry rcons) x xs
   (Recordx xs Nothing _) -> foldr (uncurry rcons) rnil xs
   (Tickx n x _) -> buildNat x tick n

findM:: Monad m => String -> (a -> m Bool) -> [a] -> m a
findM mes p [] = fail mes
findM mes p (x:xs) =
  do { b <- p x
     ; if b then return x else findM mes p xs}

buildExt :: (Show c,Show b,Monad m) => String -> (b -> c,b -> c -> c,b -> c -> c -> c,b -> c -> c -> c -> c) ->
                      Extension c -> [SynExt b] -> m c
buildExt loc (lift0,lift1,lift2,lift3) x ys =
  do { y <- findM ("\nAt "++loc++
                   "\nCan't find a "++extName x++" syntax extension called: '"++
                   extKey x++"', for "++show x++"\n  "++plistf show "" ys "\n  " "")
                  (matchExt loc x) ys
     ; case (x,y) of
        (Listx xs (Just x) _,Lx(tag,nil,cons)) -> return(foldr (lift2 cons) x xs)
        (Listx xs Nothing  _,Lx(tag,nil,cons)) -> return(foldr (lift2 cons) (lift0 nil) xs)
        (Listx xs (Just x) _,Ix(tag,Just(nil,cons),_,_,_,_)) -> return(foldr (lift2 cons) x xs)
	(Listx xs Nothing  _,Ix(tag,Just(nil,cons),_,_,_,_)) -> return(foldr (lift2 cons) (lift0 nil) xs)

        (Recordx xs (Just x) _,Rx(tag,nil,cons)) -> return(foldr (uncurry(lift3 cons)) x xs)
        (Recordx xs Nothing  _,Rx(tag,nil,cons)) -> return(foldr (uncurry(lift3 cons)) (lift0 nil) xs)
        (Recordx xs (Just x) _,Ix(tag,_,_,_,Just(nil,cons),_)) -> return(foldr (uncurry(lift3 cons)) x xs)
        (Recordx xs Nothing  _,Ix(tag,_,_,_,Just(nil,cons),_)) -> return(foldr (uncurry(lift3 cons)) (lift0 nil) xs)

        (Tickx 0 x _,Tx(tag,tick)) -> return x
        (Tickx n x _,Tx(tag,tick)) -> return(buildNat x (lift1 tick) n)
        (Tickx n x _,Ix(tag,_,_,_,_,Just tick)) -> return(buildNat x (lift1 tick) n)
        
        (Numx n (Just x) _,Nx(tag,zero,succ)) -> return(buildNat x (lift1 succ) n)
        (Numx n Nothing  _,Nx(tag,zero,succ)) -> return(buildNat (lift0 zero) (lift1 succ) n)
        (Numx n (Just x) _,Ix(tag,_,Just(zero,succ),_,_,_)) -> return(buildNat x (lift1 succ) n)
        (Numx n Nothing  _,Ix(tag,_,Just(zero,succ),_,_,_)) -> return(buildNat (lift0 zero) (lift1 succ) n)        
        
        (Pairx xs _,Px(tag,pair)) -> return(buildTuple (lift2 pair) xs)
        (Pairx xs _,Ix(tag,_,_,Just pair,_,_)) -> return(buildTuple (lift2 pair) xs)        
        
        _ -> fail ("\nSyntax extension: "++extKey x++" doesn't match use, at "++loc)}

buildNat :: Num a => b -> (b -> b) -> a -> b
buildNat z s 0 = z
buildNat z s n = s(buildNat z s (n-1))

buildTuple pair [] = error "No empty tuples: ()"
buildTuple pair [p] = p
buildTuple pair [x,y] = pair x y
buildTuple pair (x:xs) = pair x (buildTuple pair xs)

flat2 [] = []
flat2 ((a,b):xs) = a : b : flat2 xs

-----------------------------------------------------------------------
-- extensions for predefined data structures

listx = Ix("",Just("[]",":"),Nothing,Nothing,Nothing,Nothing) -- Lx("","[]",":")
natx = Ix("n",Nothing,Just("Z","S"),Nothing,Nothing,Nothing)  -- Nx("n","Z","S")
pairx = Ix("",Nothing,Nothing,Just "(,)",Nothing,Nothing)     -- Px("","(,)")
recordx = Ix("",Nothing,Nothing,Nothing,Just("Rnil","Rcons"),Nothing) -- Rx("","Rnil","Rcons")
tickx tag tick = Ix(tag,Nothing,Nothing,Nothing,Nothing,Just tick) 

normalList (Lx("","[]",":")) = True
normalList (Ix("",Just("[]",":"),_,_,_,_)) = True
normalList _ = False

-----------------------------------------------------
-- recognizing extension tags

listExt c (Lx _) = True
listExt c (Ix(_,Just(i,j),_,_,_,_)) = c==i || c==j
listExt c _ = False

natExt c (Nx _) = True
natExt c (Ix(_,_,Just(i,j),_,_,_)) = c==i || c==j
natExt c _ = False

pairExt c (Px _) = True
pairExt c (Ix(_,_,_,Just i,_,_)) = c==i
pairExt c _ = False

recordExt c (Rx _) = True
recordExt c (Ix(_,_,_,_,Just(i,j),_)) = c==i || c==j
recordExt c _ = False

tickExt c (Tx _) = True
tickExt c (Ix(_,_,_,_,_,Just i)) = c==i
tickExt c _ = False

------------------------------------------------------
-- Recognizing Extension constructors

listCons c (Lx(k,nil,cons)) = c==cons
listCons c (Ix(k,Just(nil,cons),_,_,_,_)) = c==cons
listCons c _ = False

listNil c (Lx(k,nil,cons)) = c==nil
listNil c (Ix(k,Just(nil,cons),_,_,_,_)) = c==nil
listNil c _ = False

natZero c (Nx(k,z,s)) = c==z
natZero c (Ix(k,_,Just(z,s),_,_,_)) = c==z
natZero c _ = False

natSucc c (Nx(k,z,s)) = c==s
natSucc c (Ix(k,_,Just(z,s),_,_,_)) = c==s
natSucc c _ = False

pairProd c (Px(k,prod)) = c==prod
pairProd c (Ix(k,_,_,Just prod,_,_)) = c==prod
pairProd c _ = False

recordCons c (Rx(k,nil,cons)) = c==cons
recordCons c (Ix(k,_,_,_,Just(nil,cons),_)) = c==cons
recordCons c _ = False

recordNil c (Rx(k,nil,cons)) = c==nil
recordNil c (Ix(k,_,_,_,Just(nil,cons),_)) = c==nil
recordNil c _ = False

tickSucc c (Tx(k,succ)) = c==succ
tickSucc c (Ix(k,_,_,_,_,Just succ)) = c==succ
tickSucc c _ = False

-----------------------------------------------------------
-- Parsers for Syntactic Extensions
--  #"abc"   [x,y; zs]i   #4  4i   (2+x)i    (a,b,c)i  {a=Int,b=String; r}i

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
   do { f <- try(incr p) <|> try(seqX p) <|> try(tickP p)
      ; tag <- many lower
      ; return(f tag)}
incr p =
   do { lexeme (char '(')
      ; n <- lexeme natNoSpace
      ; symbol "+"; x <- p
      ; char ')'
      ; return(Numx n (Just x))}
tickP p =
   do { lexeme (char '(')
      ; x <- p
      ; symbol "`"; 
      ; n <- lexeme natNoSpace
      ; char ')'
      ; return(Tickx n x)}      
      
seqX p =
  do { lexeme (char '(')
     ; xs <- sepBy p comma
     ; char ')'
     ; return(Pairx xs)}

natP :: Parser (Extension a)
natP = try $ lexeme $
       (do{ satisfy ('#'==); n <- natNoSpace; return(Numx n Nothing "n")}) <|>
       (do{ n <- natNoSpace; tag <- many lower; return(Numx n Nothing tag)})

---------------------------------------------------------------------

foldx (f@(l,n,p,r,t)) (Ix(k,Just x,nx,px,rx,tx)) = 
  l x : foldx f (Ix(k,Nothing,nx,px,rx,tx))
foldx (f@(l,n,p,r,t)) (Ix(k,Nothing,Just x,px,rx,tx)) = 
  n x : foldx f (Ix(k,Nothing,Nothing,px,rx,tx))
foldx (f@(l,n,p,r,t)) (Ix(k,Nothing,Nothing,Just x,rx,tx)) = 
  p x : foldx f (Ix(k,Nothing,Nothing,Nothing,rx,tx))  
foldx (f@(l,n,p,r,t)) (Ix(k,Nothing,Nothing,Nothing,Just x,tx)) = 
  r x : foldx f (Ix(k,Nothing,Nothing,Nothing,Nothing,tx))  
foldx (f@(l,n,p,r,t)) (Ix(k,Nothing,Nothing,Nothing,Nothing,Just x)) = 
  t x : foldx f (Ix(k,Nothing,Nothing,Nothing,Nothing,Nothing))
foldx f _ = []

makex (f@(lf,nf,pf,rf,tf)) [] x = x
makex (f@(lf,nf,pf,rf,tf)) (Lx x: xs) (Ix(k,l,n,p,r,t)) = makex f xs (Ix(k,Just(lf x),n,p,r,t))
makex (f@(lf,nf,pf,rf,tf)) (Nx x: xs) (Ix(k,l,n,p,r,t)) = makex f xs (Ix(k,l,Just(nf x),p,r,t))
makex (f@(lf,nf,pf,rf,tf)) (Px x: xs) (Ix(k,l,n,p,r,t)) = makex f xs (Ix(k,l,n,Just(pf x),r,t))
makex (f@(lf,nf,pf,rf,tf)) (Rx x: xs) (Ix(k,l,n,p,r,t)) = makex f xs (Ix(k,l,n,p,Just(rf x),t))
makex (f@(lf,nf,pf,rf,tf)) (Tx x: xs) (Ix(k,l,n,p,r,t)) = makex f xs (Ix(k,l,n,p,r,Just(tf x)))
makex f (x:xs) i = makex f xs i


wExt = Ix("w",Just("Nil","Cons"),Just("Zero","Succ"),Just("Pair"),Just("RNil","RCons"),Just("Next"))


mergex [] x = x
mergex (Lx(_,a,b): xs) (Ix(k,l,n,p,r,t)) = mergex xs (Ix(k,Just(a,b),n,p,r,t))
mergex (Nx(_,a,b): xs) (Ix(k,l,n,p,r,t)) = mergex xs (Ix(k,l,Just(a,b),p,r,t))
mergex (Px(_,a)  : xs) (Ix(k,l,n,p,r,t)) = mergex xs (Ix(k,l,n,Just a,r,t))
mergex (Rx(_,a,b): xs) (Ix(k,l,n,p,r,t)) = mergex xs (Ix(k,l,n,p,Just(a,b),t))
mergex (Tx(_,a)  : xs) (Ix(k,l,n,p,r,t)) = mergex xs (Ix(k,l,n,p,r,Just a))
mergex (x:xs) i = mergex xs i

mergey ("List",[a,b])   (Ix(k,l,n,p,r,t)) = (Ix(k,Just(a,b),n,p,r,t))
mergey ("Nat",[a,b])    (Ix(k,l,n,p,r,t)) = (Ix(k,l,Just(a,b),p,r,t))
mergey ("Pair",[a])     (Ix(k,l,n,p,r,t)) = (Ix(k,l,n,Just a,r,t))
mergey ("Record",[a,b]) (Ix(k,l,n,p,r,t)) = (Ix(k,l,n,p,Just(a,b),t))
mergey ("Tick",[a])     (Ix(k,l,n,p,r,t)) = (Ix(k,l,n,p,r,Just a))
mergey _                i                 = i

-----------------------------------------------------------
-- check that in a syntactic extension like:
-- deriving syntax(i) List(A,B) Nat(C,D) Tick(G)
-- that the constructors (A,B,C,D,G) have the correct arity for 
-- the extension they belong to (0,2,   0,1,   1)
--                               List   Nat    Tick

-- for each extension, the name of the roles, and their expected arities

expectedArities =
  [("List"  ,[("Nil    ",0),("Cons   ",2::Int)])
  ,("Nat"   ,[("Zero   ",0),("Succ   ",1)])
  ,("Pair"  ,[("Pair   ",2)])
  ,("Record",[("RecNil ",0),("RecCons",3)])
  ,("Tick"  ,[("Tick   ",1)])
  ]

-- Check a list of arities agianst the expected arities, indicate with
-- (False,_) if 1) arities don't match
--              2) there are extra constructors with no cooresponding role
--              3) there are two few constructors for the roles of that extension

checkArities [] [] = []
checkArities ((c,n):xs) ((d,m):ys) = (n==m,(c,show n,d,show m)): checkArities xs ys
checkArities [] ((d,m):ys) = (False,("       "," ",d++"  unexpected extra constructor",show m)): checkArities [] ys
checkArities ((c,n):xs) [] = (False,(c,show n,"?  missing constructor","?")): checkArities xs []

-- If the extension name doesn't fit, report an error

badName name = Right ("\n'"++name++"' is not a valid syntactic extension name, choose from: "++
                     plistf fst "" expectedArities ", " ".\n")

-- Check a list of extensions, and build a Ix synExt data structure                     

checkMany :: String -> [(String,[(String,Int)])] -> Either (SynExt String) String
checkMany tag [] = Left (Ix(tag,Nothing,Nothing,Nothing,Nothing,Nothing))
checkMany tag ((name,args):more) =
  case checkMany tag more of
    Right x -> Right x
    Left info -> 
         case lookup name expectedArities of
           Nothing -> badName name 
           Just expected ->  if not good then Right s else Left info'
             where ans = checkArities expected args
                   good = all fst ans
                   g (bool,(c,n,d,m)) = concat["\n     ",c," ",n,"           ",m,"     ",d]
                   s = concat(["\nError in syntactic extension declaration ",name
                             ,plistf fst "(" args "," ")"
                             ,"\n     Expected           Actual"
                             ,"\n     Role   Arity       Arity  Constructor\n"]++ map g ans)
                   info' = mergey (name,map fst args) info
                   
liftEither (Left x) = return x
liftEither (Right x) = fail x
     
                                
              
       

go x = case checkMany "tag" x of
        Left x -> putStrLn(show x)
        Right y -> putStrLn y

--go [("List",[("N",0),("C",2)]),("Nat",[("Z",0),("S",1)])]                        
                     
{-
f (x,y) = [x,y]
g x = [x]
h = (f,f,g,f,g)
test x = foldx h x
w=Ix("",Just("[]",":"),Nothing,Nothing,Just("Z","S"),Nothing)
-}