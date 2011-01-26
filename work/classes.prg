-- simulate classes as propositions first

-- issue 87:
--isFunctor :: (* ~> *) ~> (* ~> *)
--{isFunctor []} = []


isFunctor :: (* ~> *) ~> Prop
{isFunctor []} = Success


prop Functor :: (* ~> *) ~> * where
  Lfunctor :: Functor []
  Tfunctor :: Functor Tree
--  Lfunctor :: Functor a {isFunctor a}

prop Monad' :: (* ~> *) ~> * where
  M :: Functor a => Monad' a


data Tree a = Node a | Fork (Tree a) (Tree a)


data Test :: * where
  Test :: forall (a :: * ~> *) (t :: *) . Monad' a => a t -> Test


