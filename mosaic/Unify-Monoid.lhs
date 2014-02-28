
> {-# LANGUAGE TypeFamilies, DataKinds, PolyKinds, GADTs, ConstraintKinds, FlexibleInstances #-}
> import GHC.Exts
> import GHC.TypeLits
> import Data.Monoid

let's have stuff of this form:

> data Stuff :: (k -> Constraint) -> k -> * where

Stuff can be atomic

>   Atom :: c k => Stuff c k

or joined

>   Join :: Stuff c k -> Stuff c k' -> Stuff c (Join c k k')

We did not say what Join (on the type level) is

> type family Join (c :: k -> Constraint) (a :: k) (a' :: k) :: k

Use the popular hiding trick

> data Hidden :: (k -> *) -> * where
>   Hide :: p a -> Hidden p

This way it can form a Monoid

> instance Monoid (Hidden (Stuff c)) where
>   Hide a `mappend` Hide b = Hide $ a `Join` b

A small demo

> class KnownSymbol (s :: Symbol)
> instance KnownSymbol "Hey"
> instance KnownSymbol "Du"

> demo :: Hidden (Stuff KnownSymbol)
> demo = Hide (Atom :: Stuff KnownSymbol "Hey") <> Hide (Atom :: Stuff KnownSymbol "Du")