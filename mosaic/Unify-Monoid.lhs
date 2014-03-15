
> {-# LANGUAGE TypeFamilies, DataKinds, PolyKinds, GADTs, ConstraintKinds, FlexibleInstances
>            , TypeOperators #-}

> import GHC.Exts
> import GHC.TypeLits
> import Data.Monoid
> import Data.Proxy

let's have stuff of this form:

> data Stuff :: (k -> Constraint) -> St k -> * where

Stuff can be atomic

>   Atom :: c k => Stuff c (A k)

or joined

>   Join :: Stuff c k -> Stuff c k' -> Stuff c (Join c k k')

and then there are variables

>   Var :: c k => Stuff c (V k)

We did not say what Join (on the type level) is

> type family Join (c :: k -> Constraint) (a :: St k) (a' :: St k) :: St k

Use the popular hiding trick

> data Hidden :: (k -> *) -> * where
>   Hide :: p a -> Hidden p

This way it can form a Monoid

> instance Monoid (Hidden (Stuff c)) where
>   Hide a `mappend` Hide b = Hide $ a `Join` b

A small demo

> {-class KnownSymbol (s :: Symbol)
> instance KnownSymbol "Hey"
> instance KnownSymbol "Du"
> instance KnownSymbol "a"
> -}

> data St a = V a | A a | St a `J` St a

> type VarSymbol s = Stuff KnownSymbol (V s)
> type AtomSymbol s = Stuff KnownSymbol (A s)

> demo, demo2 :: Hidden (Stuff KnownSymbol)
> demo = Hide (Atom :: AtomSymbol "Hey") <> Hide (Atom :: AtomSymbol "Du")
> demo2 = Hide (Var :: VarSymbol "a") <> Hide (Atom :: AtomSymbol "Du")

This corresponds to (Hey Du)

> instance Show (Hidden (Stuff KnownSymbol)) where
>   show (Hide x) = go x where
>                 go :: Stuff KnownSymbol ss -> String
>                 go a@Atom = "(Atom :: AtomSymbol " ++ show (SomeSymbol $ some a) ++ ")"
>                 go v@Var = "(Var :: VarSymbol " ++ show (SomeSymbol $ some v) ++ ")"
>                 go (l `Join` r) = go l ++ " `Join` " ++ go r
>                 some :: Stuff KnownSymbol (x s) -> Proxy s
>                 some Atom = Proxy
>                 some Var = Proxy

> {-NOT NOW! instance Show (Hidden (Stuff KnownSymbol)) where
>   showsPrec p (Hide x) = go p x where
>                 go :: Int -> Stuff KnownSymbol s -> ShowS
>                 go p a@Atom = "(Atom :: Stuff KnownSymbol " ++ show (SomeSymbol $ some a) ++ ")"
>                 go p v@Var = "(Var :: Stuff KnownSymbol " ++ show (SomeSymbol $ some v) ++ ")"
>                 go p (l `Join` r) = go l ++ " `Join` " ++ go r
>                 some :: Stuff KnownSymbol s -> Proxy s
>                 some Atom = Proxy
>                 some Var = Proxy-}



Then we can try unify stuff, obtaining other stuff
here the vars that are free are tracked as k

> class FreeVars (l :: [Symbol])
> instance FreeVars '[]
> instance (KnownSymbol n, FreeVars ns) => FreeVars (n ': ns)

> frees :: Stuff KnownSymbol s -> Hidden (Stuff FreeVars)
> frees Atom = Hide (Atom :: Stuff FreeVars (A '[]))
> frees Var = Hide (Atom :: Stuff FreeVars (A '["heh?"]))

these will be binary (n-ary?) unifiers

demo >&< demo2

Finally these unifiers need to be joined to get a constraint system


