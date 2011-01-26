import "../src/LangPrelude.prg"

-- simulate classes as propositions first
-- later we have to deal with the operational
-- aspects (e.g. dictionary passing)
--

prop Functor :: (* ~> *) ~> * ~> * where
  Lfunctor :: Functor [] a
  Tfunctor :: Functor Tree a
  Mfunctor :: Functor Maybe a
  IOfunctor :: Functor IO a
  Pairfunctor :: Functor ((,) a) b


prop Monad' :: (* ~> *) ~> * ~> * where
  M :: Functor a b -> Monad' a b


data Tree a = Node a | Fork (Tree a) (Tree a)


data Test :: * where
  Test :: Monad' a t => Monad a -> a t -> Test


