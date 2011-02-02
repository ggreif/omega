module SyntaxExt where

import Auxillary
import List(nub)
import ParserAll  -- This for defining parsers
-- To import ParserAll you must define CommentDef.hs and TokenDef.hs
-- These should be in the same directory as this file.
import Char(isLower)

import qualified Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.HughesPJ(Doc,text,int,(<>),(<+>),($$),($+$),render)

data SyntaxStyle = OLD | NEW

type SynAssoc a = Either a a

data SynExt t -- Syntax Extension
  = Ox        -- no extension
  | Ix (String,Maybe (SynAssoc (t,t)),Maybe(t,t),Maybe (SynAssoc t),Maybe (SynAssoc (t,t)),Maybe t,Maybe t,Maybe t)
  | Parsex (String,SyntaxStyle,[(t,Int)],[(t,[t])])

data Extension t
  = Listx (SynAssoc [t]) (Maybe t) String --  [x,y ; zs]i  [x ; y,z]i
  | Natx Int (Maybe t) String         --  4i   (2+x)i
  | Pairx (SynAssoc [t]) String       --  (a,b,c)i
  | Recordx (SynAssoc [(t,t)]) (Maybe t) String  --  {x=t,y=s ; zs}i  {zs ; y=s,x=t}i
  | Tickx Int t String                --  (e`3)i
  | Unitx String                      --  ()i
  | Itemx t String                    --  (e)i

-------------------------------------------------------------
-- Show instances

instance Show a => Show (SynExt a) where
  show Ox = "Ox"
  show (Ix(k,l,n,p,r,t,u,i)) = "Ix "++k++f' "List" l++f "Nat" n++g' "Pair" p++f' "Record" r++g "Tick" t++g "Unit" u++g "Item" i
     where f nm Nothing = ""
           f nm (Just(x,y)) = " "++nm++"["++show x++","++show y++"]"
           f' nm (Just (Right x)) = f nm (Just x)
           f' nm (Just (Left x)) = f ("Left"++nm) (Just x)
           f' _ Nothing = ""
           g nm Nothing = ""
           g nm (Just x) = " "++nm++"["++show x++"]"
           g' nm Nothing = ""
           g' nm (Just (Right x)) = g nm (Just x)
           g' nm (Just (Left x)) = g ("Left"++nm) (Just x)
  show (Parsex(k,_,_,zs)) = "Px "++k++show zs           

instance Show x => Show(Extension x) where
  show (Listx ts' Nothing tag) = plist "[" ts "," ("]"++tag)
    where (_, ts) = outLR ts'
  show (Listx (Right ts) (Just t) tag) = plist "[" ts "," "; " ++ show t ++"]"++tag
  show (Listx (Left ts) (Just t) tag) = "[" ++ show t ++ "; " ++ plist "" ts "," ("]"++tag)
  show (Natx n Nothing tag) = show n++tag
  show (Natx n (Just t) tag) = "("++show n++"+"++show t++")"++tag
  show (Unitx tag) = "()"++tag
  show (Itemx x tag) = "("++show x++")"++tag
  show (Pairx ts' tag) = "("++ help ts ++")"++tag
    where help [] = ""
          help [x] = show x
          help (x:xs) = show x++","++help xs
          (_, ts) = outLR ts'
  show (Recordx ts' Nothing tag) = plistf f "{" ts "," ("}"++tag)
    where f (x,y) = show x++"="++show y
          (_, ts) = outLR ts'
  show (Recordx (Right ts) (Just ys) tag) =  plistf f "{" ts "," (";"++show ys++"}"++tag)
    where f (x,y) = show x++"="++show y
  show (Recordx (Left ts) (Just ys) tag) =  "{" ++ show ys ++ "; " ++ plistf f "" ts "," ("}"++tag)
    where f (x,y) = show x++"="++show y
  show (Tickx n t tag) = "("++show t++"`"++show n++")"++tag

extKey :: Extension a -> String
extKey (Listx xs _ s) = s
extKey (Recordx xs _ s) = s
extKey (Natx n _ s) = s
extKey (Unitx s) = s
extKey (Itemx x s) = s
extKey (Pairx xs s) = s
extKey (Tickx n x s) = s


extName :: Extension a -> String
extName (Listx (Right xs) _ s) = "List"
extName (Listx (Left xs) _ s) = "LeftList"
extName (Recordx (Right xs) _ s) = "Record"
extName (Recordx (Left xs) _ s) = "LeftRecord"
extName (Natx n _ s) = "Nat"
extName (Unitx s) = "Unit"
extName (Itemx _ s) = "Item"
extName (Pairx (Right xs) s) = "Pair"
extName (Pairx (Left xs) s) = "LeftPair"
extName (Tickx n _ s) = "Tick"


outLR (Right xs) = (Right, xs)
outLR (Left xs) = (Left, xs)

----------------------------------------------------
-- Creating formatted documents

ppExt :: (a -> Doc) -> Extension a -> Doc
ppExt f((Listx (Right xs) (Just x) s)) = PP.sep (PP.lbrack: PP.punctuate PP.comma (map f xs)++[PP.semi,f x,text ("]"++s)])
ppExt f((Listx (Left xs) (Just x) s)) = PP.sep (PP.lbrack: f x: PP.semi: PP.punctuate PP.comma (map f xs)++[text ("]"++s)])
ppExt f((Listx xs' Nothing s)) = PP.sep (PP.lbrack: PP.punctuate PP.comma (map f xs)++[text ("]"++s)])
                                 where (_, xs) = outLR xs'
ppExt f((Natx n (Just x) s)) = PP.hcat [PP.lparen,PP.int n,text "+",f x,text (")"++s)]
ppExt f((Natx n Nothing s)) = PP.hcat [PP.int n,text s]
ppExt f((Unitx s)) = text ("()"++s)
ppExt f((Itemx x s)) = PP.lparen <> f x <> text (")"++s)
ppExt f((Pairx xs' s)) = PP.lparen <> PP.hcat(PP.punctuate PP.comma (map f xs)) <> text (")"++s)
  where (_, xs) = outLR xs'
ppExt f((Recordx (Right xs) (Just x) s)) = text "{" <> PP.hcat(PP.punctuate PP.comma (map g xs)) <> PP.semi <> f x <> text ("}"++s)
  where g (x,y) = f x <> text "=" <> f y
ppExt f((Recordx (Left xs) (Just x) s)) = text "{" <> f x <> PP.semi <> PP.hcat(PP.punctuate PP.comma (map g xs)) <> text ("}"++s)
  where g (x,y) = f x <> text "=" <> f y
ppExt f (Recordx xs' Nothing s) = text "{" <> PP.hcat(PP.punctuate PP.comma (map g xs)) <> text ("}"++s)
  where g (x,y) = f x <> text "=" <> f y
        (_, xs) = outLR xs'
ppExt f((Tickx n x s)) = PP.hcat [PP.lparen,f x,text "`",PP.int n,text (")"++s)]


-------------------------------------------------------
-- map and fold-like operations

extList :: Extension a -> [a]
extList ((Listx (Right xs) (Just x) _)) = x:xs
extList ((Listx (Left xs) (Just x) _)) = foldr (:) [x] xs
extList ((Listx xs' Nothing _)) = xs
  where (_, xs) = outLR xs'
extList ((Recordx (Right xs) (Just x) _)) = (x: flat2 xs)
extList ((Recordx (Left xs) (Just x) _)) = foldr (:) [x] (flat2 xs)
extList ((Recordx xs' Nothing _)) = flat2 xs
  where (_, xs) = outLR xs'
extList ((Natx n (Just x) _)) = [x]
extList ((Natx n Nothing _)) = []
extList ((Unitx _)) = []
extList ((Itemx x _)) = [x]
extList ((Pairx xs' _)) = xs
  where (_, xs) = outLR xs'
extList ((Tickx n x _)) = [x]

instance Eq t => Eq (Extension t) where
 (Listx (Right ts1) (Just t1) s1) == (Listx (Right xs1) (Just x1) s2) = s1==s2 && (t1:ts1)==(x1:xs1)
 (Listx (Left ts1) (Just t1) s1) == (Listx (Left xs1) (Just x1) s2) = s1==s2 && (t1:ts1)==(x1:xs1)
 (Listx ts1 Nothing s1) == (Listx xs1 Nothing s2) = s1==s2 && ts1==xs1
 (Natx n (Just t1) s1) == (Natx m (Just x1) s2) = s1==s2 && t1==x1 && n==m
 (Natx n Nothing s1) == (Natx m Nothing s2) = s1==s2 && n==m
 (Unitx s) == (Unitx t) = s==t
 (Itemx x s) == (Itemx y t) = x==y && s==t
 (Pairx xs s) == (Pairx ys t) = xs==ys && s==t
 (Recordx (Right ts1) (Just t1) s1) == (Recordx (Right xs1) (Just x1) s2) = s1==s2 && t1==x1 && ts1==xs1
 (Recordx (Left ts1) (Just t1) s1) == (Recordx (Left xs1) (Just x1) s2) = s1==s2 && t1==x1 && ts1==xs1
 (Recordx ts1 Nothing s1) == (Recordx xs1 Nothing s2) = s1==s2 && ts1==xs1
 (Tickx n t1 s1) == (Tickx m x1 s2) = s1==s2 && t1==x1 && n==m
 _ == _ = False

extM :: Monad a => (b -> a c) -> Extension b -> a (Extension c)
extM f (Listx (Right xs) (Just x) s) = do { ys <- mapM f xs; y <- f x; return((Listx (Right ys) (Just y) s))}
extM f (Listx (Left xs) (Just x) s) = do { y <- f x; ys <- mapM f xs; return((Listx (Left ys) (Just y) s))}
extM f (Listx xs' Nothing s) = do { ys <- mapM f xs; return((Listx (lr ys) Nothing s))}
  where (lr, xs) = outLR xs'
extM f (Natx n (Just x) s) = do { y <- f x; return((Natx n (Just y) s))}
extM f (Natx n Nothing s) = return((Natx n Nothing s))
extM f (Unitx s) =  return(Unitx s)
extM f (Itemx x s) =  do { y <- f x; return((Itemx y s))}
extM f (Pairx xs' s) =  do { ys <- mapM f xs; return((Pairx (lr ys) s))}
  where (lr, xs) = outLR xs'
extM f (Recordx (Right xs) (Just x) s) = do { ys <- mapM g xs; y <- f x; return(Recordx (Right ys) (Just y) s)}
  where g (x,y) = do { a <- f x; b <- f y; return(a,b) }
extM f (Recordx (Left xs) (Just x) s) = do { y <- f x; ys <- mapM g xs; return(Recordx (Left ys) (Just y) s)}
  where g (x,y) = do { a <- f x; b <- f y; return(a,b) }
extM f (Recordx xs' Nothing s) = do { ys <- mapM g xs; return(Recordx (lr ys) Nothing s)}
 where g (x,y) = do { a <- f x; b <- f y; return(a,b) }
       (lr, xs) = outLR xs'
extM f (Tickx n x s) = do { y <- f x; return((Tickx n y s))} 


threadL f [] n = return([],n)
threadL f (x:xs) n =
  do { (x',n1) <- f x n
     ; (xs',n2) <- threadL f xs n1
     ; return(x' : xs', n2)}

threadPair f (x,y) n = do { (a,n1) <- f x n; (b,n2) <- f y n1; return((a,b),n2)}

extThread :: Monad m => (b -> c -> m(d,c)) -> c -> Extension b -> m(Extension d,c)
extThread f n (Listx (Right xs) (Just x) s) =
  do { (ys,n1) <- threadL f xs n; (y,n2) <- f x n1; return(Listx (Right ys) (Just y) s,n2)}
extThread f n (Listx (Left xs) (Just x) s) =
  do { (y,n1) <- f x n; (ys,n2) <- threadL f xs n1; return(Listx (Left ys) (Just y) s,n2)}
extThread f n (Listx xs' Nothing s) =
  do { (ys,n1) <- threadL f xs n; return(Listx (lr ys) Nothing s,n1)}
    where (lr, xs) = outLR xs'
extThread f n (Natx m (Just x) s) = do { (y,n1) <- f x n; return(Natx m (Just y) s,n1)}
extThread f n (Natx m Nothing s) = return(Natx m Nothing s,n)
extThread f n (Unitx s) =  return(Unitx s,n)
extThread f n (Itemx x s) =  do { (y,n1) <- f x n; return(Itemx y s,n1)}
extThread f n (Pairx xs' s) =  do { (ys,n1) <- threadL f xs n; return(Pairx (lr ys) s,n1)}
  where (lr, xs) = outLR xs'
extThread f n (Recordx (Right xs) (Just x) s) =
  do { (ys,n1) <- threadL (threadPair f) xs n; (y,n2) <- f x n1; return(Recordx (Right ys) (Just y) s,n2)}
extThread f n (Recordx (Left xs) (Just x) s) =
  do { (y,n1) <- f x n; (ys,n2) <- threadL (threadPair f) xs n1; return(Recordx (Left ys) (Just y) s,n2)}
extThread f n (Recordx xs' Nothing s) =
  do { (ys,n1) <- threadL (threadPair f) xs n; return(Recordx (lr ys) Nothing s,n1)}
    where (lr, xs) = outLR xs'
extThread f n (Tickx m x s) = do { (y,n1) <- f x n; return(Tickx m y s,n1)}

cross f (x,y) = (f x,f y)

instance Functor Extension where
  fmap f (Listx xs' (Just x) s) = (Listx (lr (map f xs)) (Just(f x)) s)
    where (lr, xs) = outLR xs'
  fmap f (Listx xs' Nothing s) = (Listx (lr (map f xs)) Nothing s)
    where (lr, xs) = outLR xs'
  fmap f (Natx n (Just x) s) = (Natx n (Just (f x)) s)
  fmap f (Natx n Nothing s) = (Natx n Nothing s)
  fmap f (Unitx s) =  (Unitx s)
  fmap f (Itemx x s) =  (Itemx (f x) s)
  fmap f (Pairx xs' s) =  (Pairx (lr $ map f xs) s)
    where (lr, xs) = outLR xs'
  fmap f (Recordx xs' (Just x) s) = (Recordx (lr (map (cross f) xs)) (Just(f x)) s)
    where (lr, xs) = outLR xs'
  fmap f (Recordx xs' Nothing s) = (Recordx (lr (map (cross f) xs)) Nothing s)
    where (lr, xs) = outLR xs'
  fmap f (Tickx n x s) = (Tickx n (f x) s)

--------------------------------------------------------
-- Other primitive operations like selection and equality

-- Equal if the same kind and the same key
instance Eq a => Eq (SynExt a) where
  Ox == Ox = True
  (Ix(k1,_,_,_,_,_,_,_)) == (Ix(k2,_,_,_,_,_,_,_)) = k1==k2
  (Parsex(k1,_,_,_)) == (Parsex(k2,_,_,_)) = k1==k2
  _ == _ = False

synKey Ox = ""
synKey (Ix (s,_,_,_,_,_,_,_)) = s
synKey (Parsex(s,_,_,_)) = s

synName Ox = ""
synName (Ix (s,Just(Right _),_,_,_,_,_,_)) = "List"
synName (Ix (s,Just(Left _),_,_,_,_,_,_)) = "LeftList"
synName (Ix (s,_,Just _,_,_,_,_,_)) = "Nat"
synName (Ix (s,_,_,Just(Right _),_,_,_,_)) = "Pair"
synName (Ix (s,_,_,Just(Left _),_,_,_,_)) = "LeftPair"
synName (Ix (s,_,_,_,Just(Right _),_,_,_)) = "Record"
synName (Ix (s,_,_,_,Just(Left _),_,_,_)) = "LeftRecord"
synName (Ix (s,_,_,_,_,Just _,_,_)) = "Tick"
synName (Ix (s,_,_,_,_,_,Just _,_)) = "Unit"
synName (Ix (s,_,_,_,_,_,_,Just _)) = "Item"
synName (Parsex (s,_,_,_)) = "Parse"



-- Both the name and the type match. Different types (i.e. List,Nat,Pair)
-- can use the same name.

matchExt (Listx (Right _) _ s)   (Ix(t,Just(Right _),_,_,_,_,_,_)) | s==t = return True
matchExt (Listx (Left _) _ s)   (Ix(t,Just(Left _),_,_,_,_,_,_)) | s==t = return True
matchExt (Natx _ _ s)    (Ix(t,_,Just _,_,_,_,_,_)) | s==t = return True
matchExt (Unitx s)       (Ix(t,_,_,_,_,_,Just _,_)) | s==t = return True
matchExt (Itemx _ s)     (Ix(t,_,_,_,_,_,_,Just _)) | s==t = return True
matchExt (Pairx (Right _) s)     (Ix(t,_,_,Just(Right _),_,_,_,_)) | s==t = return True
matchExt (Pairx (Left _) s)     (Ix(t,_,_,Just(Left _),_,_,_,_)) | s==t = return True
matchExt (Recordx (Right _) _ s) (Ix(t,_,_,_,Just(Right _),_,_,_)) | s==t = return True
matchExt (Recordx (Left _) _ s) (Ix(t,_,_,_,Just(Left _),_,_,_)) | s==t = return True
matchExt (Tickx _ _ s)   (Ix(t,_,_,_,_,Just _,_,_)) | s==t = return True
matchExt _ _                = return False

----------------------------------------------------------
-- Building such objects in an abstract manner

findM:: Monad m => String -> (a -> m Bool) -> [a] -> m a
findM mes p [] = fail mes
findM mes p (x:xs) =
  do { b <- p x
     ; if b then return x else findM mes p xs}

-- harmonizeExt: correct inevitable little errors that happened during parsing
harmonizeExt x@(Listx (Right xs) Nothing s) ys = case findM "" (matchExt x') ys of
                                                  Nothing -> return x
                                                  Just _ -> return x'
                                                 where x' = Listx (Left xs) Nothing s
harmonizeExt x@(Listx (Right [h]) (Just t) s) ys = case findM "" (matchExt x') ys of
                                                    Nothing -> return x
                                                    Just _ -> return x'
                                                   where x' = Listx (Left [t]) (Just h) s

harmonizeExt x@(Recordx (Right xs) Nothing s) ys = case findM "" (matchExt x') ys of
                                                    Nothing -> return x
                                                    Just _ -> return x'
                                                   where x' = Recordx (Left xs) Nothing s

harmonizeExt x@(Pairx (Right xs) s) ys = case findM "" (matchExt x') ys of
                                          Nothing -> return x
                                          Just _ -> return x'
                                         where x' = Pairx (Left xs) s

harmonizeExt x _ = return x

rot3 f a b c = f c a b

buildExt :: (Show c,Show b,Monad m) => String -> (b -> c,b -> c -> c,b -> c -> c -> c,b -> c -> c -> c -> c) ->
                      Extension c -> [SynExt b] -> m c
buildExt loc (lift0,lift1,lift2,lift3) x ys =
  do { x <- harmonizeExt x ys
     ; y <- findM ("\nAt "++loc++
                   "\nCan't find a "++extName x++" syntax extension called: '"++
                   extKey x++"', for "++show x++"\n  "++plistf show "" ys "\n  " "")
                  (matchExt x) ys
     ; case (x,y) of
        (Listx (Right xs) (Just x) _,Ix(tag,Just(Right(nil,cons)),_,_,_,_,_,_)) -> return(foldr (lift2 cons) x xs)
        (Listx (Left xs) (Just x) _,Ix(tag,Just(Left(nil,cons)),_,_,_,_,_,_)) -> return(foldr (flip $ lift2 cons) x (reverse xs))
        (Listx (Right xs) Nothing  _,Ix(tag,Just(Right(nil,cons)),_,_,_,_,_,_)) -> return(foldr (lift2 cons) (lift0 nil) xs)
        (Listx (Left xs) Nothing  _,Ix(tag,Just(Left(nil,cons)),_,_,_,_,_,_)) -> return(foldr (flip $ lift2 cons) (lift0 nil) (reverse xs))
        (Recordx (Right xs) (Just x) _,Ix(tag,_,_,_,Just(Right(nil,cons)),_,_,_)) -> return(foldr (uncurry(lift3 cons)) x xs)
        (Recordx (Left xs) (Just x) _,Ix(tag,_,_,_,Just(Left(nil,cons)),_,_,_)) -> return(foldr (uncurry(rot3 $ lift3 cons)) x (reverse xs))
        (Recordx (Right xs) Nothing  _,Ix(tag,_,_,_,Just(Right(nil,cons)),_,_,_)) -> return(foldr (uncurry(lift3 cons)) (lift0 nil) xs)
        (Recordx (Left xs) Nothing  _,Ix(tag,_,_,_,Just(Left(nil,cons)),_,_,_)) -> return(foldr (uncurry(rot3 $ lift3 cons)) (lift0 nil) (reverse xs))
        (Tickx n x _,Ix(tag,_,_,_,_,Just tick,_,_)) -> return(buildNat x (lift1 tick) n)
        (Natx n (Just x) _,Ix(tag,_,Just(zero,succ),_,_,_,_,_)) -> return(buildNat x (lift1 succ) n)
        (Natx n Nothing  _,Ix(tag,_,Just(zero,succ),_,_,_,_,_)) -> return(buildNat (lift0 zero) (lift1 succ) n)        
        (Unitx _,Ix(tag,_,_,_,_,_,Just unit,_)) -> return(buildUnit (lift0 unit))
        (Itemx x _,Ix(tag,_,_,_,_,_,_,Just item)) -> return(buildItem (lift1 item) x)
        (Pairx (Right xs) _,Ix(tag,_,_,Just(Right pair),_,_,_,_)) -> return(buildTuple (lift2 pair) xs)
        (Pairx (Left xs) _,Ix(tag,_,_,Just(Left pair),_,_,_,_)) -> return(buildTuple (flip $ lift2 pair) (reverse xs))                
        _ -> fail ("\nSyntax extension: "++extKey x++" doesn't match use, at "++loc)}

buildNat :: Num a => b -> (b -> b) -> a -> b
buildNat z s 0 = z
buildNat z s n = s(buildNat z s (n-1))

buildUnit unit = unit

buildItem item i = item i

buildTuple pair [] = error "No empty tuples: ()"
buildTuple pair [p] = p
buildTuple pair [x,y] = pair x y
buildTuple pair (x:xs) = pair x (buildTuple pair xs)

flat2 [] = []
flat2 ((a,b):xs) = a : b : flat2 xs

-----------------------------------------------------------------------
-- extensions for predefined data structures

listx = Ix("",Just$Right("[]",":"),Nothing,Nothing,Nothing,Nothing,Nothing,Nothing) -- Lx("","[]",":")
natx = Ix("n",Nothing,Just("Z","S"),Nothing,Nothing,Nothing,Nothing,Nothing)  -- Nx("n","Z","S")
pairx = Ix("",Nothing,Nothing,Just$Right "(,)",Nothing,Nothing,Nothing,Nothing)     -- Px("","(,)")
recordx = Ix("",Nothing,Nothing,Nothing,Just$Right("Rnil","Rcons"),Nothing,Nothing,Nothing) -- Rx("","Rnil","Rcons")
tickx tag tick = Ix(tag,Nothing,Nothing,Nothing,Nothing,Just tick,Nothing,Nothing) 

normalList (Ix("",Just(Right("[]",":")),_,_,_,_,_,_)) = True
normalList _ = False

------------------------------------------------------
-- Recognizing Extension constructors

listCons c (Ix(k,Just(Right(nil,cons)),_,_,_,_,_,_)) = c==cons
listCons c _ = False

listNil c (Ix(k,Just(Right(nil,cons)),_,_,_,_,_,_)) = c==nil
listNil c _ = False

leftListCons c (Ix(k,Just(Left(nil,cons)),_,_,_,_,_,_)) = c==cons
leftListCons c _ = False

leftListNil c (Ix(k,Just(Left(nil,cons)),_,_,_,_,_,_)) = c==nil
leftListNil c _ = False

natZero c (Ix(k,_,Just(z,s),_,_,_,_,_)) = c==z
natZero c _ = False

natSucc c (Ix(k,_,Just(z,s),_,_,_,_,_)) = c==s
natSucc c _ = False

unitUnit c (Ix(k,_,_,_,_,_,Just unit,_)) = c==unit
unitUnit c _ = False

itemItem c (Ix(k,_,_,_,_,_,_,Just item)) = c==item
itemItem c _ = False

pairProd c (Ix(k,_,_,Just(Right prod),_,_,_,_)) = c==prod
pairProd c _ = False

leftPairProd c (Ix(k,_,_,Just(Left prod),_,_,_,_)) = c==prod
leftPairProd c _ = False


recordCons c (Ix(k,_,_,_,Just(Right(nil,cons)),_,_,_)) = c==cons
recordCons c _ = False

recordNil c (Ix(k,_,_,_,Just(Right(nil,cons)),_,_,_)) = c==nil
recordNil c _ = False

leftRecordCons c (Ix(k,_,_,_,Just(Left(nil,cons)),_,_,_)) = c==cons
leftRecordCons c _ = False

leftRecordNil c (Ix(k,_,_,_,Just(Left(nil,cons)),_,_,_)) = c==nil
leftRecordNil c _ = False

tickSucc c (Ix(k,_,_,_,_,Just succ,_,_)) = c==succ
tickSucc c _ = False

-- recognizing extension tags

listExt c x = listCons c x || listNil c x
leftListExt c x = leftListCons c x || leftListNil c x
natExt c x = natZero c x || natSucc c x
recordExt c x = recordCons c x || recordNil c x
leftRecordExt c x = leftRecordCons c x || leftRecordNil c x

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

semiHeadSeq left right head elem buildf =
  do { lexeme left
     ; x <- head
     ; semi
     ; xs <- sepBy elem comma
     ; right  -- No lexeme here because the tag must follow immediately
     ; tag <- many (lower <|> char '\'')
     ; return(buildf (Just x) xs tag)}

extP :: Parser a -> Parser (Extension a)
extP p = try(lexeme(try(listP p) <|> leftListP p <|> parensP p <|> try(recP p) <|> leftRecP p))
  where listP p = semiTailSeq (char '[') (char ']') p p (\xs x t -> Listx (Right xs) x t)
        leftListP p = semiHeadSeq (char '[') (char ']') p p (\x xs t -> Listx (Left xs) x t)
        recP p = semiTailSeq (char '{') (char '}') pair p (\xs x t -> Recordx (Right xs) x t)
          where pair = do { x <- p; symbol "="; y <- p; return(x,y)}
        leftRecP p = semiHeadSeq (char '{') (char '}') p pair (\x xs t -> Recordx (Left xs) x t)
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
      ; return(Natx n (Just x))}

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
     ; return(pairlike xs)}
  where pairlike xs "" = Pairx (Right xs) ""
        pairlike [] tag = Unitx tag
        pairlike [x] tag = Itemx x tag
        pairlike xs tag = Pairx (Right xs) tag

natP :: Parser (Extension a)
natP = try $ lexeme $
       (do{ satisfy ('#'==); n <- natNoSpace; return(Natx n Nothing "n")}) <|>
       (do{ n <- natNoSpace; tag <- many lower; return(Natx n Nothing tag)})

---------------------------------------------------------------------

mergey ("List",[a,b])     (Ix(k,Nothing,n,p,r,t,u,i)) = Ix(k,Just$Right(a,b),n,p,r,t,u,i)
mergey ("LeftList",[a,b]) (Ix(k,Nothing,n,p,r,t,u,i)) = Ix(k,Just$Left(a,b),n,p,r,t,u,i)
mergey ("Nat",[a,b])      (Ix(k,l,Nothing,p,r,t,u,i)) = Ix(k,l,Just(a,b),p,r,t,u,i)
mergey ("Unit",[a])       (Ix(k,l,n,p,r,t,Nothing,i)) = Ix(k,l,n,p,r,t,Just a,i)
mergey ("Item",[a])       (Ix(k,l,n,p,r,t,u,Nothing)) = Ix(k,l,n,p,r,t,u,Just a)
mergey ("Pair",[a])       (Ix(k,l,n,Nothing,r,t,u,i)) = Ix(k,l,n,Just$Right a,r,t,u,i)
mergey ("LeftPair",[a])   (Ix(k,l,n,Nothing,r,t,u,i)) = Ix(k,l,n,Just$Left a,r,t,u,i)
mergey ("Record",[a,b])   (Ix(k,l,n,p,Nothing,t,u,i)) = Ix(k,l,n,p,Just$Right(a,b),t,u,i)
mergey ("LeftRecord",[a,b]) (Ix(k,l,n,p,Nothing,t,u,i)) = Ix(k,l,n,p,Just$Left(a,b),t,u,i)
mergey ("Tick",[a])       (Ix(k,l,n,p,r,Nothing,u,i)) = Ix(k,l,n,p,r,Just a,u,i)
mergey _                  i                           = i

-----------------------------------------------------------
-- check that in a syntactic extension like:
-- deriving syntax(i) List(A,B) Nat(C,D) Tick(G)
-- that the constructors (A,B,C,D,G) have the correct arity for 
-- the extension they belong to (0,2,   0,1,   1)
--                               List   Nat    Tick

-- for each extension, the name of the roles, and their expected arities

expectedArities =
  [("List",Just "LeftList",[("Nil    ",0),("Cons   ",2::Int)])
  ,("LeftList",Just "List",[("Nil    ",0),("Snoc   ",2)])
  ,("Nat"     ,Nothing    ,[("Zero   ",0),("Succ   ",1)])
  ,("Unit"    ,Nothing    ,[("Unit   ",0)])
  ,("Item"    ,Nothing    ,[("Item   ",1)])
  ,("Pair",Just "LeftPair",[("Pair   ",2)])
  ,("LeftPair",Just "Pair",[("Pair   ",2)])
  ,("Record",Just "LeftRecord",[("RecNil ",0),("RecCons",3)])
  ,("LeftRecord",Just "Record",[("RecNil ",0),("RecSnoc",3)])
  ,("Tick"    ,Nothing    ,[("Tick   ",1)])
  ]

-- Check a list of arities against the expected arities, indicate with
-- (False,_) if 1) arities don't match
--              2) there are extra constructors with no corresponding role
--              3) there are too few constructors for the roles of that extension

checkArities name style expected actual =
     case (expected,actual) of
       ([],[]) -> []
       ((c,n):xs,(d,m):ys) -> (n==m,(c,show n,d,show m),arityfix (n==m) d)
                            : checkArities name style xs ys
       ([]      ,(d,m):ys) -> (False,("       "," ",d++"  unexpected extra constructor",show m),extrafix style d)
                            : checkArities name style [] ys
       ((c,n):xs,[]      ) -> (False,(c,show n,"?    - missing role.","?"),missingfix style c)
                            : checkArities name style xs []
  where suffix OLD = " from the deriving clause."
        suffix NEW = " from the constructors of the data declaration."
        arityfix True  d = ""
        arityfix False d = "Fix the arity of "++d++" in the data declaration."
        extrafix OLD d = "Remove, extra constructor "++detrail d++" from the data declaration."
        extrafix NEW d = "Remove, extra constructor "++detrail d++" from the syntax clause for "++name++"."
        missingfix OLD c = "Add a constructor for "++detrail c++" to the data declaration."
        missingfix NEW c = "Add a constructor for "++detrail c++" to the syntax clause for "++name++"."
                
suggestFix style [] = ""
suggestFix style ((True,_,fix): xs) = suggestFix style xs
suggestFix style ((False,_,fix): xs) = "\n   "++fix ++ suggestFix style xs
  
detrail xs = reverse (dropWhile (==' ') (reverse xs))

fstOfTriple (x,y,z) = x

dropMid (x,y,z) = (x,z)

-- If the extension name doesn't fit, report an error

badName name = Right ("\n'"++name++"' is not a valid syntactic extension name, choose from: "++
                     plistf fstOfTriple "" expectedArities ", " ".\n")

reportRepeated name = Just ("'"++name++"' syntactic extension cannot be specified twice.")

reportIncompatible (name, Just reversed, _) = Just ("'"++name++"' and '"++reversed++"' syntactic extensions cannot be specified together.")

wellFormed (("List",_,_):_) (name@"List") (Ix(tag,Just(Right _),_,_,_,_,_,_)) = reportRepeated name
wellFormed (syn@("List",Just _, _):_) "List" (Ix(tag,Just(Left _),_,_,_,_,_,_)) = reportIncompatible syn
wellFormed (("LeftList",_,_):_) (name@"LeftList") (Ix(tag,Just(Left _),_,_,_,_,_,_)) = reportRepeated name
wellFormed (syn@("LeftList", Just no, _):_) "LeftList" (Ix(tag,Just(Right _),_,_,_,_,_,_)) = reportIncompatible syn
wellFormed (("Nat",_,_):_) (name@"Nat") (Ix(tag,_,Just _,_,_,_,_,_)) = reportRepeated name
wellFormed (("Unit",_,_):_) (name@"Unit") (Ix(tag,_,_,_,_,_,Just _,_)) = reportRepeated name
wellFormed (("Item",_,_):_) (name@"Item") (Ix(tag,_,_,_,_,_,_,Just _)) = reportRepeated name
wellFormed (("Pair",_,_):_) (name@"Pair") (Ix(tag,_,_,Just(Left _),_,_,_,_)) = reportRepeated name
wellFormed (syn@("Pair",Just _,_):_) "Pair" (Ix(tag,_,_,Just(Right _),_,_,_,_)) = reportIncompatible syn
wellFormed (("LeftPair",_,_):_) (name@"LeftPair") (Ix(tag,_,_,Just(Right _),_,_,_,_)) = reportRepeated name
wellFormed (syn@("LeftPair",Just _,_):_) "LeftPair" (Ix(tag,_,_,Just(Left _),_,_,_,_)) = reportIncompatible syn
wellFormed (("Record",_,_):_) (name@"Record") (Ix(tag,_,_,_,Just(Right _),_,_,_)) = reportRepeated name
wellFormed (syn@("Record",Just _,_):_) "Record" (Ix(tag,_,_,_,Just(Left _),_,_,_)) = reportIncompatible syn
wellFormed (("LeftRecord",_,_):_) (name@"LeftRecord") (Ix(tag,_,_,_,Just(Left _),_,_,_)) = reportRepeated name
wellFormed (syn@("LeftRecord",Just _,_):_) "LeftRecord" (Ix(tag,_,_,_,Just(Right _),_,_,_)) = reportIncompatible syn
wellFormed (("Tick",_,_):_) (name@"Tick") (Ix(tag,_,_,_,_,Just _,_,_)) = reportRepeated name
wellFormed (_:rest) name info = wellFormed rest name info
wellFormed [] _ _ = Nothing

-- Check a list of extensions, and build a Ix synExt data structure                     

checkMany :: SyntaxStyle -> String -> [(String,[(String,Int)])] -> Either (SynExt String) String
checkMany style tag [] = Left (Ix(tag,Nothing,Nothing,Nothing,Nothing,Nothing,Nothing,Nothing))
checkMany style tag ((name,args):more) =
  case checkMany style tag more of
    Right x -> Right x
    Left info -> 
         case (lookup name (map dropMid expectedArities), wellFormed expectedArities name info) of
           (Nothing, _) -> badName name
           (_, Just problem) -> Right problem
           (Just expected, _) -> if not good then Right s else Left info'
             where ans = checkArities name style expected args
                   good = all fstOfTriple ans
                   printname = case style of
                                 OLD -> name++"("++tag++")"
                                 NEW -> name++ plistf fst "(" args "," ")"
                   g (bool,(c,n,d,m),fix) = concat["\n     ",c," ",n,"           ",m,"     ",d]
                   s = concat(["\nError in syntactic extension declaration ",printname
                             ,"\n     Expected           Actual"
                             ,"\n     Role   Arity       Arity  Constructor\n"]
                             ++ map g ans) ++ fixes
                   fixes = if good then "" else "\n\nPossible fix(es):" ++ suggestFix style ans
                   info' = mergey (name,map fst args) info
duplicates [] = []
duplicates (x:xs) = nub(if elem x xs then x : duplicates xs else duplicates xs)
                   
liftEither (Left x) = return x
liftEither (Right x) = fail x



checkClause arityCs (name,args) = 
   do { let printname = name++plistf id "(" args "," ")"
      ; ys <- mapM (computeArity printname arityCs) args
      ; return(name,ys) }                                   
        
computeArity printname arityCs c =
  case lookup c arityCs of
    Nothing -> fail (concat["\nThe name "++c++", in the syntax derivation "
                       ,printname,",\nis not amongst the declared"
                       ," constructors: ",plistf fst "" arityCs ", " ".\n"])
    Just n -> return (c,n)
      
wExt = Ix("w",Just$Right("Nil","Cons"),Just("Zero","Succ"),Just$Right "Pair",Just$Right("RNil","RCons"),Just "Next",Just "Unit",Just "Item")

                                              
go x = case checkMany OLD "tag" x of
        Left x -> putStrLn(show x)
        Right y -> putStrLn y

 
