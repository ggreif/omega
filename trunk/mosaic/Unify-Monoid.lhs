
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

and then there are variables

>   Var :: c k => Stuff c k

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
> instance KnownSymbol "a"

> demo, demo2 :: Hidden (Stuff KnownSymbol)
> demo = Hide (Atom :: Stuff KnownSymbol "Hey") <> Hide (Atom :: Stuff KnownSymbol "Du")
> demo2 = Hide (Var :: Stuff KnownSymbol "a") <> Hide (Atom :: Stuff KnownSymbol "Du")

This corresponds to (Hey Du)

TODO: need show instance

Then we can try unify stuff, obtaining other stuff
here the vars that are free are tracked as k

> class FreeVars (l :: [Symbol])

these will be binary (n-ary?) unifiers

demo >&< demo2

Finally these unifiers need to be joined to get a constraint system


