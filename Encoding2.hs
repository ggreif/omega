-- Copyright (c) Tim Sheard
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Tue Apr 25 12:54:27 Pacific Daylight Time 2006
-- Omega Interpreter: version 1.2.1

module Encoding2 where

import Maybe
import Monads
import Monad (liftM)
import RankN
import Syntax
import Value
import List(union)
import Bind

type Symbol = Name

class Generic t where
   typeOf :: t -> Tau

instance Generic () where
  typeOf x = unitT

instance Generic Int where
  typeOf x = intT

instance Generic Char where
  typeOf x = charT

instance Generic Float where
  typeOf x = floatT

instance Generic Bool where
  typeOf x = boolT

instance Generic Symbol where
  typeOf x = symbolT

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

data Hidden f = forall a . Hide (f a)
instance Generic (a Int) => Generic (Hidden a) where
  typeOf x = thidden f
    where deref :: Hidden f -> f Int
          deref = undefined
          TyApp f int = (typeOf (deref x))

instance Generic a => Generic (Maybe a) where
  typeOf x = tmaybe(typeOf(fromJust x))


-------------------------------------------------

class Encoding t where
   to   :: t -> V
   toList :: [t] -> V
   from :: V -> t
   fromList :: V -> [t]
   toList = consUp
   fromList = consDown


consUp :: Encoding a => [a] -> V
consUp [] = Vcon (Global "[]") []
consUp (x:xs) = Vcon (Global ":") [(to x),(consUp xs)]

toStr :: String -> V
toStr x = consUp x

consDown :: Encoding a => V -> [a]
consDown (Vcon (Global "[]") []) = []
consDown (Vcon (Global ":") [x,xs]) = (from x) : (consDown xs)
consDown v = error ("Value not a list in from List: "++(show v))

consDownf :: Encoding a => (V -> a) -> V -> [a]
consDownf f (Vcon (Global "[]") []) = []
consDownf f (Vcon (Global ":") [x,xs]) = (f x) : (consDown xs)
consDownf f v = error ("Value not a list in from List: "++(show v))

lift1 name f = Vprimfun name (analyzeWith g)
  where g v = f v

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
			e <- runFIO fio (\_ _ _ msg -> fail msg)
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
    from v = error ("Value not an function: "++(show v))
-}

-- for functions without monadic ranges (FIO a) we can always turn them into V
-- but its impossible to pull functions back from V with those types. Here
-- are three functions for the forward path

to1 :: (Encoding a, Encoding b) => (a -> b) -> V
to2 :: (Encoding a, Encoding b, Encoding c) => (a -> c -> b) -> V
to3 :: (Encoding a, Encoding b, Encoding c, Encoding d) => (a -> d -> b -> c) -> V

lazy_to1 f = Vprimfun "lazy1" (return . to  . f . from)
lazy_to2 f = Vprimfun "lazy2" (return . lazy_to1  . f . from)

to1 f = Vprimfun "to1" (analyzeWith(return . to  . f . from))  -- (a -> b) -> V
to2 f = Vprimfun "to2" (analyzeWith(return . to1 . f . from))  -- (a -> b -> c) -> V
to3 f = Vprimfun "to3" (analyzeWith(return . to2 . f . from))  -- (a -> b -> c -> d) -> V

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
    from v = error ("Value not an Char: "++(show v))

instance Encoding Bool where
    to True = (Vcon (Global "True") [])
    to False = (Vcon (Global "False") [])
    from (Vcon (Global "True") []) = True
    from (Vcon (Global "False") []) = False
    from v = error ("Value not Bool: "++(show v))

instance Encoding a => Encoding (Maybe a) where
    to Nothing = Vcon (Global "Nothing") []
    to (Just x) = Vcon (Global "Just") [to x]
    from (Vcon (Global "Nothing") []) = Nothing
    from (Vcon (Global "Just") [x]) = from x
    from v = error ("Value not a Maybe type: "++show v)

instance (Encoding a,Encoding b) => Encoding (a,b) where
    to (a,b) = Vprod (to a) (to b)
    from (Vprod x y) = (from x,from y)
    from v = error ("Value not an pair: "++(show v))

instance (Encoding a,Encoding b,Encoding c) => Encoding (a,b,c) where
    to (a,b,c) = Vprod (to a) (Vprod (to b) (to c))
    from (Vprod x (Vprod y z)) = (from x,from y,from z)
    from v = error ("Value not an triple: "++(show v))

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

instance Generic A where
   typeOf x = TyVar name1 star
instance Generic B where
   typeOf x = TyVar name2 star
instance Generic C where
   typeOf x = TyVar name3 star

genOf :: Tau -> [Name]
genOf (TyVar nm k) = [nm]
genOf (TyApp x y) = union (genOf x) (genOf y) where f (x,_) (y,_) = x==y
genOf _ = []

gen :: Tau -> Sigma
gen t = Forall (mk (genOf t) t)
  where mk [] t = Nil ([],Rtau t)
        mk (n:ns) t =  Cons (star,All) (bind n (mk ns t))

instance Show A where
  show (A x) = show x

