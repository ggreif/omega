{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses, TypeFamilies #-}

import Data.Monoid

class (Monoid a, Monad m, a ~ m i) => Bag m a i | a -> m i where
  into :: i -> Bag m a i

--class Monad (Bag m a) where
--  return = into