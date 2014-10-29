{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, TypeFamilies #-}

import Data.Monoid hiding ((<>))

class (Monoid a, Monad m, a ~ m i) => Bag m a i | a -> i where
  into :: i -> m i
  into = return
  (<>) :: a -> a -> a
  (<>) = mappend

--class Monad (Bag m a) where
--  return = into

instance Monoid (IO ()) where
  mempty = return ()
  mappend = (>>)

instance Bag IO (IO ()) ()

test1 :: Bag m a i => a
test1 = mempty

test2 :: Bag IO a () => a
test2 = do a <- putStrLn "Hey"
           b <- into a
           putStrLn "You"

class (i ~ (), Bag m a i) => API m a i | a -> i where
  silly :: String -> m ()
  nilly :: Bool -> a -> a -> a

test3 :: API m (m ()) () => m ()
test3 = do silly "You"
           nilly True (silly "a") $ do
              silly "else"
              (silly "more" <> silly "of it")

instance API IO (IO ()) () where
  silly s = putStrLn $ ("A silly " ++ s)
  nilly b t e = if b then t else e
