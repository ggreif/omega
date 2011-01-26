-- simulate classes as propositions first

-- issue 87:
--isFunctor :: (* ~> *) ~> (* ~> *)
--{isFunctor []} = []


isFunctor :: (* ~> *) ~> Prop
{isFunctor []} = Success


prop Functor :: (* ~> *) ~> * ~> * where
  Lfunctor :: Functor [] a
  Tfunctor :: Functor Tree a
  Pairfunctor :: Functor ((,) a) b
--  Pairfunctor :: Functor c a -> Functor c b -> Functor c (a,b)


prop Monad' :: (* ~> *) ~> * ~> * where
  M :: Functor a b -> Monad' a b


data Tree a = Node a | Fork (Tree a) (Tree a)


data Test :: * where
  Test :: forall (a :: * ~> *) (t :: *) . Monad' a t => a t -> Test


