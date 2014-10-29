{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, TypeFamilies #-}

import Data.Monoid hiding ((<>))

-- We would like to work in a monoid, but obtain the `do` syntax for free
--  Additionally we would like to have a reifiable monad.
--  See http://www.cse.chalmers.se/~joels/writing/bb.pdf

--class (Monoid a, Monad m, a ~ m i) => Bag m a i | a -> i where
class (Monoid a, Monad m, a ~ m i) => Bag m a i where
  into :: i -> m i
  into = return
  (<>) :: a -> a -> a
  (<>) = mappend

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

class (i ~ (), Bag m a i) => API m a i where
  silly :: String -> m ()
  nilly :: Bool -> a -> a -> a

--test3 :: API m (m ()) () => Bool -> m ()
test3 :: API m a i => Bool -> a
test3 b = do silly "You"
             nilly b (silly "a") $ do
                silly "else"
                (silly "more" <> silly "of it")

instance API IO (IO ()) () where
  silly s = putStrLn $ ("A silly " ++ s)
  nilly b t e = if b then t else e
