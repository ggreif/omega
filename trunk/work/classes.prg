import "../src/LangPrelude.prg"

-- simulate classes as propositions first


prop Functor :: (* ~> *) ~> * ~> * where
  Lfunctor :: Functor [] a
  Tfunctor :: Functor Tree a
  Mfunctor :: Functor Maybe a
  Pairfunctor :: Functor ((,) a) b


prop Monad' :: (* ~> *) ~> * ~> * where
  M :: Functor a b -> Monad' a b


data Tree a = Node a | Fork (Tree a) (Tree a)


data Test :: * where
  Test :: Monad' a t => Monad a -> a t -> Test


