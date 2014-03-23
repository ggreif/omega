
> {-# LANGUAGE TypeFamilies, DataKinds, PolyKinds, GADTs, ConstraintKinds, FlexibleInstances
>            , TypeOperators, FlexibleContexts #-}

> import GHC.Exts
> import GHC.TypeLits
> import Data.Monoid
> import Data.Proxy
> import Data.Type.Equality(type (==), (:~:)(Refl))

let's have stuff of this form:

> data Stuff :: (k -> Constraint) -> St k -> * where

Stuff can be atomic

>   Atom :: c k => Stuff c (A k)

or joined

>   Join :: Stuff c k -> Stuff c k' -> Stuff c (k `J` k')

and then there are variables

>   Var :: c k => Stuff c (V k)

Use the popular hiding trick

> data Hidden :: (k -> *) -> * where
>   Hide :: p a -> Hidden p

This way it can form a Monoid

> instance Monoid (Hidden (Stuff c)) where
>   --mempty = Hide Var
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

> data SingList :: [k] -> * where
>   Nil :: SingList '[]
>   Cons :: proxy n -> SingList ns -> SingList (n ': ns)

> class FreeVars (l :: [Symbol]) where
>   ell :: Maybe (SingList l)
>   ell = Nothing
> instance FreeVars '[]
> instance (KnownSymbol n, FreeVars ns, (n `In` ns) ~ '[]) => FreeVars (n ': ns) where
>   ell = Nothing

> type family Frees (st :: St Symbol) :: St [Symbol] where
>   Frees (A s) = V '[]
>   Frees (V s) = V '[s]
>   Frees (V s `J` V s') = V '[s, s']
>   Frees (s `J` s') = Frees s `J` Frees s'

> type family In (el :: k) (coll :: [k]) :: [k] where
>   In a '[] = '[]
>   In a (a ': as) = a ': In a as
>   In b (a ': as) = In b as

> --try :: Stuff KnownSymbol s -> Stuff FreeVars ss -> Maybe (Stuff FreeVars (s ': ss))
> --try Var 

> {-
> data FreeLike :: [Symbol] -> * where
>   Empty :: FreeLike '[]
>   Can :: FreeVars (n ': ns) => FreeLike ns -> FreeLike (n ': ns)
>   Can't :: KnownSymbol n => FreeLike ns -> FreeLike (n ': ns)
> -}

> join :: Stuff FreeVars (V '[a] `J` V '[b]) -> Maybe (Stuff FreeVars (V '[a, b]))
> join (a@Var `Join` b@Var) = case prox a `sameSymbol` prox b of
>                  Just Refl -> Nothing
>                  Nothing -> undefined
>   where prox :: Stuff FreeVars (V '[a]) -> Proxy a
>         prox Var = Proxy

> frees :: Stuff KnownSymbol s -> Stuff FreeVars (Frees s)
> frees Atom = Var
> frees Var = Var
> --frees (a `Join` b) = frees a `Join` frees b
> frees (Var `Join` Var) = Var

these will be binary (n-ary?) unifiers

demo >&< demo2

Finally these unifiers need to be joined to get a constraint system


