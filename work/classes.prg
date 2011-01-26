-- simulate classes as propositions first

-- issue 87:
--isFunctor :: (* ~> *) ~> (* ~> *)
--{isFunctor []} = []


isFunctor :: (* ~> *) ~> Prop
{isFunctor []} = Success


prop Functor :: (* ~> *) ~> Prop ~> * where
  Lfunctor :: Functor [] Success
--  Lfunctor :: Functor a {isFunctor a}

prop Monad' :: (* ~> *) ~> Prop ~> * where
  M :: Functor a Success => Monad' a Success


data Tree a = Node a | Fork (Tree a) (Tree a)


--data Test :: forall (a :: * ~> *) . Monad' a Success => a ~> * where
data Test :: * where
  Test :: forall (a :: * ~> *) (t :: *) . Monad' a Success => a t -> Test


