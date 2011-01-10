{-# LANGUAGE TypeSynonymInstances #-}
module Encoding where

import Maybe
import Monads
import Monad (liftM)
import RankN
import Syntax
import Value
import List(unionBy)
import Bind
import SyntaxExt(SynExt(..),listx,normalList)

type Symbol = Name

class Generic t where
   typeOf :: t -> Tau
   
instance Generic () where
  typeOf x = unitT

instance Generic Int where
  typeOf x = intT

instance Generic Char where
  typeOf x = charT

instance Generic Ordering where
  typeOf x = orderingT
  
instance Generic Float where
  typeOf x = floatT

instance Generic Bool where
  typeOf x = boolT

instance Generic Symbol where
  typeOf x = symbolT

instance (Generic a,Generic b) => Generic (Equal a b) where
  typeOf x = teq (typeOf (leftEqual x)) (typeOf (rightEqual x))

instance (Generic a,Generic b) => Generic (a,b) where
  typeOf x = tpair (typeOf (fst x)) (typeOf (snd x))

instance (Generic a,Generic b,Generic c) => Generic (a,b,c) where
  typeOf x = tprods [ typeOf (f x),typeOf(g x),typeOf(h x) ]
       where f(x,y,z) = x
             g(x,y,z) = y
             h(x,y,z) = z

instance (Generic a,Generic b,Generic c,Generic d) => Generic (a,b,c,d) where
  typeOf x = tprods [ typeOf(e x),typeOf (f x),typeOf(g x),typeOf(h x) ]
           where e(w,x,y,z) = w
                 f(w,x,y,z) = x
                 g(w,x,y,z) = y
                 h(w,x,y,z) = z


instance Generic a => Generic [a] where
  typeOf x = tlist(typeOf (head x))

instance (Generic a,Generic b) => Generic (a->b) where
  typeOf f = tarr (typeOf (domain f)) (typeOf (range f))
    where domain :: (a->b) -> a
          domain f = undefined
          range :: (a->b) -> b
          range f = undefined

instance Generic a => Generic (IO a) where
  typeOf x = tio (typeOf (run x))
    where run :: IO a -> a
          run = undefined


newtype Ptr x = Ptr x

instance Generic a => Generic (Ptr a) where
  typeOf x = tptr (typeOf (deref x))
    where deref :: Ptr a -> a
          deref = undefined

data Eql x y = Eq x y
instance (Generic a,Generic b) => Generic (Eql a b) where
  typeOf f = teq (typeOf (fst f)) (typeOf (snd f))
    where fst :: (Eql a b) -> a
          fst f = undefined
          snd :: (Eql a b) -> b
          snd f = undefined

{-
data Hidden f = forall a . Hide (f a)
instance Generic (a Int) => Generic (Hidden a) where
  typeOf x = thidden f
    where deref :: Hidden f -> f Int
          deref = undefined
          TyApp f int = (typeOf (deref x))
-}

instance Generic a => Generic (Maybe a) where
  typeOf x = tmaybe(typeOf(fromJust x))
  
instance (Generic a, Generic b) => Generic(Either a b) where
  typeOf x = tsum (typeOf(geta x)) (typeOf(getb x))
    where geta (Left x) = x
          getb (Right x) = x


-------------------------------------------------

class Encoding t where
   to   :: t -> V
   toList :: [t] -> V
   from :: V -> t
   fromList :: V -> [t]
   toList = consUp
   fromList = consDown


consUp :: Encoding a => [a] -> V
consUp [] = Vcon (Global "[]",listx) []
consUp (x:xs) = Vcon (Global ":",listx) [(to x),(consUp xs)]

toStr :: String -> V
toStr x = consUp x

consDown :: Encoding a => V -> [a]
consDown (Vcon (Global "[]",lx) [])   | normalList lx = []
consDown (Vcon (Global ":",lx) [x,xs]) | normalList lx = (from x) : (consDown xs)
consDown v = error ("Value not a list in from List: "++(show v))

consDownf :: Encoding a => (V -> a) -> V -> [a]
consDownf f (Vcon (Global "[]",lx) [])     | normalList lx = []
consDownf f (Vcon (Global ":",lx ) [x,xs]) | normalList lx = (f x) : (consDown xs)
consDownf f v = error ("Value not a list in from List: "++(show v))

lift1 name f = Vprimfun name (analyzeWith f)

lift2 name f = Vprimfun name (analyzeWith g)
  where g v = return(lift1 (name++" "++show v) (f v))

lift3 name f = Vprimfun name (analyzeWith g)
  where g v = return(lift2 (name++" "++show v) (f v))

----------------------------------------------------------
-- Encodings

instance Encoding () where
   to x = Vlit Unit
   from (Vlit Unit) = ()
   from v = error ("Value not unit: "++(show v))

instance Encoding a => Encoding (IO a) where
   to x = Vfio [] $ do
                a <- fio x
                return (Right (to a))
   from (Vfio perm fio) = do
   -- Nathan: what to do with the permutation?  I just ignore it for now
                        e <- runFIO fio (\_ _ msg -> fail msg)
                        case e of
                          Left msg -> fail msg
                          Right a -> return (from a)

   from v = error ("Value not an IO computation: "++(show v))


{-
instance Encoding a => Encoding (FIO a) where
   to x = Vlazy(fmap to x)
   from (Vlazy x) = (fmap from x)
   from v = error ("Value not an action: "++(show v))


instance (Encoding a,Encoding b) => Encoding (a -> FIO b) where
    to f = Vprimfun "->" (return . to . f . from)
    from (Vprimfun s f) = (fmap from) . f . to
    from v = error ("Value not a function: "++(show v))
-}

-- for functions without monadic ranges (FIO a) we can always turn them into V
-- but it's impossible to pull functions back from V with those types. Here
-- are three functions for the forward path

to1 :: (Encoding a, Encoding b) => String -> (a -> b) -> V
to2 :: (Encoding a, Encoding b, Encoding c) => String -> (a -> c -> b) -> V
to3 :: (Encoding a, Encoding b, Encoding c, Encoding d) => String -> (a -> d -> b -> c) -> V

lazy_to1 name f = Vprimfun name (return . to  . f . from)
lazy_to2 name f = Vprimfun name (return . (lazy_to1 (name ++ "#"))  . f . from)

to1 name f = Vprimfun name (analyzeWith(return . to . f . from))  -- (a -> b) -> V
to2 name f = Vprimfun name (analyzeWith(return . (to1 (name ++ "#")) . f . from))  -- (a -> b -> c) -> V
to3 name f = Vprimfun name (analyzeWith(return . (to2 (name ++ "#")) . f . from))  -- (a -> b -> c -> d) -> V

instance Encoding V where
    to x = x
    from x = x

instance Encoding Symbol where
    to x = Vlit(Symbol x)
    from (Vlit (Symbol n)) = n
    from v = error ("Value not a Symbol: "++(show v))

instance Encoding Int where
    to n = Vlit(Int n)
    from (Vlit(Int n)) = n
    from v = error ("Value not an Int: "++(show v))

instance Encoding Float where
    to n = Vlit(Float n)
    from (Vlit(Float n)) = n
    from v = error ("Value not a Float: "++(show v))

instance Encoding Char where
    to n = Vlit(Char n)
    from (Vlit(Char n)) = n
    from v = error ("Value not a Char: "++(show v))

instance Encoding Bool where
    to True = (Vcon (Global "True",Ox) [])
    to False = (Vcon (Global "False",Ox) [])
    from (Vcon (Global "True",Ox) []) = True
    from (Vcon (Global "False",Ox) []) = False
    from v = error ("Value not Bool: "++(show v))

instance Encoding a => Encoding (Maybe a) where
    to Nothing = Vcon (Global "Nothing",Ox) []
    to (Just x) = Vcon (Global "Just",Ox) [to x]
    from (Vcon (Global "Nothing",Ox) []) = Nothing
    from (Vcon (Global "Just",Ox) [x]) = (Just (from x))
    from v = error ("Value not a Maybe type: "++show v)
    
    
instance Encoding Ordering where
    to EQ = Vcon (Global "EQ",Ox) []
    to LT = Vcon (Global "LT",Ox) []
    to GT = Vcon (Global "GT",Ox) []
    from (Vcon (Global "EQ",Ox) []) = EQ
    from (Vcon (Global "LT",Ox) []) = LT
    from (Vcon (Global "GT",Ox) []) = GT
    from v = error ("Value not an Ordering: "++show v)
    
    
instance (Encoding a,Encoding b) => Encoding (Either a b) where
    to (Right x) =  (Vsum R (to x))
    to (Left x) = (Vsum L (to x))
    from (Vcon (Global "L",Ox) [x]) = Left(from x)
    from (Vcon (Global "R",Ox) [x]) = Right(from x)
    from (Vsum R x) = Right(from x)
    from (Vsum L x) = Left(from x)
    from v = error ("Value not an sum (+) type: "++show v)    

instance (Encoding a,Encoding b) => Encoding (a,b) where
    to (a,b) = Vprod (to a) (to b)
    from (Vprod x y) = (from x,from y)
    from v = error ("Value not a pair: "++(show v))

instance (Encoding a,Encoding b,Encoding c) => Encoding (a,b,c) where
    to (a,b,c) = Vprod (to a) (Vprod (to b) (to c))
    from (Vprod x (Vprod y z)) = (from x,from y,from z)
    from v = error ("Value not a triple: "++(show v))

instance (Encoding a,Encoding b,Encoding c,Encoding d) => Encoding (a,b,c,d) where
    to (a,b,c,d) = Vprod (to a) (Vprod (to b) (Vprod (to c) (to d)))
    from (Vprod w (Vprod x (Vprod y z))) = (from w,from x,from y,from z)
    from v = error ("Value not a quadruple: "++(show v))


instance Encoding a => Encoding [a] where
    to x = toList x
    from x = fromList x


-----------------------------------------------------------------
-- To make the initial environment we must lift haskell objects
-- to values (V) and to their types (Ty r). To deal with polymorphism
-- we introduce several "faux" type variables which are really just
-- synomyms for V, A polymorphic function inside the interpreter just
-- manipulates V values without looking at them. So we make very simple
-- instances for them.

newtype A = A V
newtype B = B V
newtype C = C V
newtype T1 = T1 V
newtype T2 = T2 V

unsafeCast (A x) = B x

instance Encoding A where
  to (A x) = x
  from = A
instance Encoding B where
  to (B x) = x
  from = B
instance Encoding C where
  to (C x) = x
  from = C
instance Encoding T1 where
  to (T1 x) = x
  from = T1
instance Encoding T2 where
  to (T2 x) = x
  from = T2

zzz = gen(typeOf(T1 $ Vlit(Tag "z")))

instance Generic A where
   typeOf x = TyVar name1 star
instance Generic B where
   typeOf x = TyVar name2 star
instance Generic C where
   typeOf x = TyVar name3 star
instance Generic T1 where
   typeOf x = TyVar name4 (MK tagT)
instance Generic T2 where
   typeOf x = TyVar name5 (MK tagT)
   
genOf :: Tau -> [(Name,Kind)]
genOf (TyVar nm k) = [(nm,k)]
genOf (TyApp x y) = unionBy f (genOf x) (genOf y) where f (x,_) (y,_) = x==y
genOf _ = []

gen :: Tau -> Sigma
gen t = Forall (mk (genOf t) t)
  where mk [] t = Nil ([],Rtau t)
        mk ((n,k):ns) t =  Cons (k,All) (bind n (mk ns t))

instance Show A where
  show (A x) = show x

----------------------------------------
-- Labels and Tag encodings

instance Encoding (Label tag) where
    to (Label s) = Vlit (Tag s)
    from (Vlit (Tag s)) = Label s
    from v = error ("Value not a Label: "++(show v))

instance Encoding HiddenLabel where
    to (Hidden l) = Vcon (Global "HideLabel",Ox) [to l]
    from (Vcon (Global "HideLabel",_) [l]) = Hidden (from l)
    from v = error ("Value not a HiddenLabel: "++(show v))

newtype DiffLabel a b = LabelNotEq Ordering

instance Encoding (DiffLabel a b) where
  to (LabelNotEq x) = error "\n*** Error ***\n(Encoding instance) LabelNotEq is abstract and cannot be applied. \nUse sameLabel to create values of type DiffLabel."
  from (Vcon (Global "LabelNotEq",_) [l]) = LabelNotEq (from l)
  from v = error ("Value not a DiffLabel: "++(show v))

instance Generic a => Generic (Label a) where
  typeOf x = tlabel (typeOf (tagOfLabel x))

instance Generic HiddenLabel where
  typeOf x = TyCon Ox (LvSucc LvZero) "HiddenLabel" (poly star)

polyDiffLabel = K [] (simpleSigma (Karr tagT (Karr tagT (Star LvZero))))
tyconDiffLabel = TyCon Ox (LvSucc LvZero) "DiffLabel" polyDiffLabel
tDiffLabel x y = TyApp (TyApp tyconDiffLabel x) y

instance (Generic a,Generic b) => Generic (DiffLabel a b) where
  typeOf x = tDiffLabel (typeOf(geta x)) (typeOf(getb x))
    where geta :: DiffLabel a b -> a
          geta _ = undefined
          getb :: DiffLabel a b -> b
          getb _ = undefined

