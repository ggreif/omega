{-# LANGUAGE FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, TypeFamilies #-}

import Data.Monoid hiding ((<>))

class (Monoid a, Monad m, a ~ m i) => Bag m a i | a -> m i where
  into :: i -> m i
  (<>) :: a -> a -> a
  (<>) = mappend

--class Monad (Bag m a) where
--  return = into

instance Monoid (IO ()) where
  mempty = return ()
  mappend = (>>)

instance Bag IO (IO ()) () where
  into = return

test1 :: Bag m a i => a
test1 = mempty

test2 :: Bag m a i => a
test2 = do a <- putStrLn "Hey"
           b <- into a
           putStrLn "You"
