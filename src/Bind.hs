{-# LANGUAGE FlexibleInstances, UndecidableInstances, GADTs #-}
module Bind(Fresh(..),Freshen(..),Swap(..),Name,Perm
           ,Bind,bind
           ,swapM, swapsM, swapsMf
           ,M,runM
           ,unsafeUnBind,reset,name1,name2,name3,name4,name5,name2Int,integer2Name) where

import Control.Monad.Fix(MonadFix(..))
import Monads

class (Monad m, HasNext m) => Fresh m where
  fresh :: m Name

class Freshen b where
  freshen :: Fresh m => b -> m (b,[(Name,Name)])
  unbind :: (Fresh m,Swap c) => Bind b c -> m(b,c)
  unbind (B x y) = do { (x',perm) <- freshen x
                      ; return(x',swaps perm y)
                      }

class Swap b where
  swap :: Name  -> Name -> b -> b
  swap a b x = swaps [(a,b)] x
  swaps :: [(Name ,Name )] -> b -> b
  swaps [] x = x
  swaps ((a,b):ps) x = swaps ps (swap a b x)

sw :: Eq a => a -> a -> a -> a
sw x y s | x==s = y | y==s = x | True = s

-------------------------------------------------------

instance Freshen Int  where
  freshen n = return(n,[])

instance Freshen b => Freshen [b] where
  freshen xs = do { pairs <- mapM freshen xs
                  ; return (map fst pairs,concat(map snd pairs))}

instance (Freshen a,Freshen b) => Freshen (a,b) where
  freshen (x,y) = do { (x',p1) <- freshen x
                     ; (y',p2) <- freshen y
                     ; return((x',y'),p1++p2)}

-----------------------------------------------

name1 = Nm 1
name2 = Nm 2
name3 = Nm 3
name4 = Nm 4
name5 = Nm 5

type Perm = [(Name,Name)]

newtype Name = Nm Integer

instance Show Name  where
  show (Nm x) = "x" ++ (show x)

instance Eq Name  where
  (Nm x) == (Nm y) = x==y

instance Ord Name  where
  compare (Nm x) (Nm y) = compare x y

instance Swap Name  where
  swap (Nm a) (Nm b) (Nm x) = Nm(sw a b x)

instance Freshen Name where
  freshen nm = do { x <- fresh; return(x,[(nm,x)]) }

instance HasNext m => Fresh m where
  fresh = do { n <- nextInteger; return (Nm n) }

name2Int (Nm x) = x
integer2Name = Nm

----------------------------------------------
data Bind a b where
  B :: (Freshen a,Swap b) => a -> b -> Bind a b

bind :: (Freshen a,Swap b) => a -> b -> Bind a b
bind a b = B a b

unsafeUnBind (B a b) = (a,b)


instance (Freshen a,Swap a,Swap b) => Swap (Bind a b) where
  swaps perm (B x y) = B (swaps perm x) (swaps perm y)


------------------------------------------------------------
swapM :: (Monad m,Swap x) => Name -> Name -> m x -> m x
swapM a b x = do { z <- x; return(swap a b z)}

swapsM :: (Monad m,Swap x) => [(Name,Name)] -> m x -> m x
swapsM xs x = do { z <- x; return(swaps xs z)}

swapsMf xs f = \ x -> swapsM xs (f (swaps xs x))

instance Swap a => Swap (M a) where
  swaps xs comp = do { e <- comp; return(swaps xs e) }

instance Swap a => Swap (IO a) where
  swaps xs comp = do { e <- comp; return(swaps xs e) }

instance (Swap a,Swap b) => Swap (a,b) where
  swaps perm (x,y)= (swaps perm x,swaps perm y)

instance (Swap a,Swap b,Swap c) => Swap (a,b,c) where
  swaps perm (x,y,z)= (swaps perm x,swaps perm y,swaps perm z)

instance Swap Bool where
  swaps xs x = x

instance (Swap a,Swap b) => Swap (a -> b) where
  swaps perm f = \ x -> swaps perm (f (swaps perm x))

instance Swap a => Swap [a] where
  swaps perm xs = map (swaps perm) xs

instance Swap Int where
  swap x y n = n

instance Swap Integer where
  swap x y n = n

instance Swap a => Swap (Maybe a) where
  swaps [] x = x
  swaps cs Nothing = Nothing
  swaps cs (Just x) = Just(swaps cs x)

instance Swap Char where
  swaps cs c = c

instance (Swap a,Swap b) => Swap (Either a b) where
  swaps [] x = x
  swaps cs (Left x) = Left (swaps cs x)
  swaps cs (Right x) = Right (swaps cs x)

--------------------------------------
newtype M x = M (Integer -> (x,Integer))

unM (M f) = f

instance Monad M where
  return x = M (\ n -> (x,n))
  (>>=) (M h) g = M f
    where f n = let (a,n2) = h n
                    M k = g a
                in k n2

runM (M f) = fst(f 0)

instance HasNext M where
  nextInteger = M h where h n = (n,n+1)
  resetNext x = M h where h n = ((),x)

instance HasOutput M where
  outputString = error

instance MonadFix M where
  mfix = undefined

