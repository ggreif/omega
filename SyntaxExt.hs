-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Mon Apr 16 10:51:51 Pacific Daylight Time 2007
-- Omega Interpreter: version 1.4.1

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
  | Lx (String,t,t)  -- list extension like #[a,b,c]i
  | Nx (String,t,t)  -- number extension like #4i
  | Px (String,t)    -- pair extension like #(a,b)i


instance Show a => Show (SynExt a) where
  show Ox = "Ox"
  show (Lx(k,a,b)) = "Lx("++k++","++show a++","++show b++")"
  show (Nx(k,a,b)) = "Nx("++k++","++show a++","++show b++")"
  show (Px(k,a)) = "Px("++k++","++show a++")"

-- Equal if the same kind and the same key,
instance Eq a => Eq (SynExt a) where
  Ox == Ox = True
  (Lx(k1,_,_)) == (Lx(k2,_,_)) = k1==k2
  (Nx(k1,_,_)) == (Nx(k2,_,_)) = k1==k2
  (Px(k1,_)) == (Px(k2,_)) = k1==k2
  _ == _ = False


synKey Ox = ""
synKey (Lx (s,_,_)) = s
synKey (Nx (s,_,_)) = s
synKey (Px (s,_)) = s

synName Ox = ""
synName (Lx (s,_,_)) = "List"
synName (Nx (s,_,_)) = "Nat"
synName (Px (s,_)) = "Pair"


-- Both the name and the type match. Different types (i.e. List,Nat,Pair)
-- can use the same name.
matchExt loc (Listx _ _ s) (Lx(t,_,_)) | s==t = return True
matchExt loc (Numx _ _ s) (Nx(t,_,_)) | s==t = return True
matchExt loc (Pairx _ s) (Px(t,_)) | s==t = return True
matchExt loc (Cseqx s) _ = return True
matchExt loc (Listx _ _ "") _ = return False
matchExt loc (Numx _ _ "") _ = return False
matchExt loc (Pairx _ "") _ = return False
matchExt loc _ _ = return False

data Extension t
  = Listx [t] (Maybe t) String  --  #[x,y ; zs]i
  | Numx Int (Maybe t) String   --  #4i   #(2+x)i
  | Pairx [t] String            --  #(a,b,c)i
  | Cseqx String                --  #"abc"
--  | Opx String                  --  #+, #<  etc.

prefx "" = ""
prefx x = "#"

instance Show x => Show(Extension x) where
  show (Listx ts Nothing tag) = plist (prefx tag ++ "[") ts "," ("]"++tag)
  show (Listx ts (Just t) tag) = plist (prefx tag ++ "[") ts "," "; " ++ show t ++"]"++tag
  show (Numx n Nothing tag) = "#"++show n++tag
  show (Numx n (Just t) tag) = "#("++show n++"+"++show t++")"++tag
  show (Pairx ts tag) = "#("++ help ts++ ")"++tag
    where help [] = ""
          help [x] = show x
          help (x:xs) = show x++","++help xs
  show (Cseqx s) = "#"++show s

build (cons,nil,succ,zero,pair,inject) x =
  case x of
   (Listx xs (Just x) _) -> foldr cons x xs
   (Listx xs Nothing _) -> foldr cons nil xs
   (Numx n (Just x) _) -> buildNat x succ n
   (Numx n Nothing _) -> buildNat zero succ n
   (Pairx xs _) -> buildTuple pair xs
   (Cseqx s) -> inject s
--   (Opx s) -> opf s

findM:: Monad m => String -> (a -> m Bool) -> [a] -> m a
findM mes p [] = fail mes
findM mes p (x:xs) =
  do { b <- p x
     ; if b then return x else findM mes p xs}

buildExt :: Monad m => String -> (b -> c,b -> c -> c,b -> c -> c -> c,String -> m c) ->
                      Extension c -> [SynExt b] -> m c
buildExt loc (lift0,lift1,lift2,inject) x ys =
  do { y <- findM ("\nCan't find a "++extName x++" syntax extension called: "++extKey x++", at "++loc)
                  (matchExt loc x) ys
     ; case (x,y) of
        (Listx xs (Just x) _,Lx(tag,nil,cons)) -> return(foldr (lift2 cons) x xs)
        (Listx xs Nothing  _,Lx(tag,nil,cons)) -> return(foldr (lift2 cons) (lift0 nil) xs)
        (Numx n (Just x) _,Nx(tag,zero,succ)) -> return(buildNat x (lift1 succ) n)
        (Numx n Nothing  _,Nx(tag,zero,succ)) -> return(buildNat (lift0 zero) (lift1 succ) n)
        (Pairx xs _,Px(tag,pair)) -> return(buildTuple (lift2 pair) xs)
        (Cseqx s, _) -> inject s
--        (Opx s) -> opf s
        _ -> fail ("\nSyntax extension: "++extKey x++"doesn't match use, at "++loc)}

listx = Lx("","[]",":")
natx = Nx("","Z","S")
pairx = Px("","(,)")

buildNat :: Num a => b -> (b -> b) -> a -> b
buildNat z s 0 = z
buildNat z s n = s(buildNat z s (n-1))

buildTuple pair [] = error "No empty tuples: ()"
buildTuple pair [p] = p
buildTuple pair [x,y] = pair x y
buildTuple pair (x:xs) = pair x (buildTuple pair xs)

extList :: Extension a -> [a]
extList ((Listx xs (Just x) _)) = (x:xs)
extList ((Listx xs Nothing _)) = xs
extList ((Numx n (Just x) _)) = [x]
extList ((Numx n Nothing _)) = []
extList ((Pairx xs _)) = xs
extList ((Cseqx s)) = []
--extList ((Opx s)) = []

extKey :: Extension a -> String
extKey ((Listx xs (Just x) s)) = s
extKey ((Listx xs Nothing s)) = s
extKey ((Numx n (Just x) s)) = s
extKey ((Numx n Nothing s)) = s
extKey ((Pairx xs s)) = s
extKey ((Cseqx s)) = s
--extKey ((Opx s)) = s

extName :: Extension a -> String
extName ((Listx xs _ s)) = "List"
extName ((Numx n _ s)) = "Nat"
extName ((Pairx xs s)) = "Pair"
extName ((Cseqx s)) = "ChrSeq"
--extName (Opx s) = "FloatOp"

instance Eq t => Eq (Extension t) where
 (Listx ts1 (Just t1) s1) == (Listx xs1 (Just x1) s2) = s1==s2 && (t1:ts1)==(x1:xs1)
 (Listx ts1 Nothing s1) == (Listx xs1 Nothing s2) = s1==s2 && (ts1)==(xs1)
 (Numx n (Just t1) s1) == (Numx m (Just x1) s2) = s1==s2 && t1==x1 && n==m
 (Numx n Nothing s1) == (Numx m Nothing s2) = s1==s2 && n==m
 (Pairx xs s) == (Pairx ys t) = xs==ys && s==t
 (Cseqx s) == (Cseqx t) = s==t
 -- (Opx s) == (Opx t) = s==t
 _ == _ = False

extM :: Monad a => (b -> a c) -> Extension b -> a (Extension c)
extM f (Listx xs (Just x) s) = do { ys <- mapM f  xs; y<- f  x;return((Listx ys (Just y) s))}
extM f (Listx xs Nothing s) = do { ys <- mapM f  xs; return((Listx ys Nothing s))}
extM f (Numx n (Just x) s) = do { y<- f  x; return((Numx n (Just y) s))}
extM f (Numx n Nothing s) = return((Numx n Nothing s))
extM f (Pairx xs s) =  do { ys <- mapM f  xs; return((Pairx ys s))}
extM f (Cseqx s) = return ( (Cseqx s))
--extM f (Opx s) = return ( (Opx s))

threadL f n [] = return([],n)
threadL f n (x:xs) =
  do { (x',n1) <- f x n
     ; (xs',n2) <- threadL f n1 xs
     ; return(x' : xs', n2)}

extThread :: Monad m => (b -> c -> m(d,c)) -> c -> Extension b -> m(Extension d,c)
extThread f n (Listx xs (Just x) s) =
  do { (ys,n1) <- threadL f n xs; (y,n2) <- f x n1; return(Listx ys (Just y) s,n2)}
extThread f n (Listx xs Nothing s) =
  do { (ys,n1) <- threadL f n xs; return(Listx ys Nothing s,n1)}
extThread f n (Numx m (Just x) s) = do { (y,n1) <- f x n; return(Numx m (Just y) s,n1)}
extThread f n (Numx m Nothing s) = return(Numx m Nothing s,n)
extThread f n (Pairx xs s) =  do { (ys,n1) <- threadL f n xs; return(Pairx ys s,n1)}
extThread f n (Cseqx s) = return (Cseqx s,n)
--extThread f n (Opx s) = return (Opx s,n)

instance Functor Extension where
  fmap f (Listx xs (Just x) s) = (Listx (map f xs) (Just(f x)) s)
  fmap f (Listx xs Nothing s) = (Listx (map f xs) Nothing s)
  fmap f (Numx n (Just x) s) = (Numx n (Just (f x)) s)
  fmap f (Numx n Nothing s) = (Numx n Nothing s)
  fmap f (Pairx xs s) =  (Pairx (map f xs) s)
  fmap f (Cseqx s) = (Cseqx s)
--  fmap f (Opx s) = (Opx s)

-----------------------------------------------------------
-- Parsers for syntactic Extensions
--  #"abc"   #[x,y ; zs]i   #4i   #(2+x)i    #(a,b,c)i

extP :: Parser a -> Parser (Extension a)
extP p =  try(lexeme(satisfy ('#'==) >> (stringP <|> natP <|> listP <|> parensP)))
  where stringP = do{ s <- stringLiteral; return(Cseqx s)}

        natP = do{ n <- natNoSpace; tag <- many lower; return(Numx n Nothing tag)}
        listP = do { lexeme lbr; f <- partsP; rbr; tag <- many lower; return(f tag)}
        partsP = do { xs <- sepBy p comma
                    ; x <- (do { semi; y <- p; return(Just y)}) <|> (return Nothing)
                    ; return(Listx xs x)}
        parensP = do { lexeme lp; f <- incr <|> seq; rp; tag <- many lower; return(f tag)}
        incr = try(do { n <- lexeme natNoSpace; symbol "+"; x <- p; return(Numx n (Just x))})
        seq = do { xs <- sepBy p comma; return(Pairx xs)}
        lp = satisfy ('('==)
        rp = satisfy (')'==)
        lbr = satisfy ('['==)
        rbr = satisfy (']'==)
constructorName = lexeme (try construct)
  where construct = do{ c <- upper
                      ; cs <- many (identLetter tokenDef)
                      ; return (c:cs) }
                    <?> "Constructor name"

ppExt :: (a -> Doc) -> Extension a -> Doc
ppExt f((Listx xs (Just x) s)) = PP.sep ((text "#["):(map f xs)++[text ";",f x,text ("]"++s)])
ppExt f((Listx xs Nothing s)) = PP.sep ((text "#["):(map f xs)++[text ("]"++s)])
ppExt f((Numx n (Just x) s)) = PP.hcat [text "#(",PP.int n,text "+",f x,text (")"++s)]
ppExt f((Numx n Nothing s)) = PP.hcat [text "#",PP.int n,text s]
ppExt f((Pairx xs s)) = text "(" <> PP.hcat(PP.punctuate PP.comma (map f xs)) <> text (")"++s)
ppExt f((Cseqx s)) = text "#" <> PP.doubleQuotes (text s)

