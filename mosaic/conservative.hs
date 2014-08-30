{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

class Datatype d where
  moduleName :: d -> String
  datatypeName :: d -> String


data Foo
data Foo'
instance Datatype Foo where
  moduleName = const "Hey"
  datatypeName = const "Foo"

class Constructor c where
  constructorName :: (Datatype d, c ~ f d) => c -> String


data C1 d -- = HHH

hhh :: C1 Foo
hhh = undefined -- HHH

instance Constructor (C1 Foo) where
  constructorName = const "C1"
