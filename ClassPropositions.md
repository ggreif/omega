# Introduction #

Section 20 (Types as Propositions) of the Users' Guide mentions that static propositions are propagated and discharged in the same way as class constraints in Haskell. This gives me the idea to actually **implement** type classes as `prop`.

But there is a dynamic (i.e. _value_) aspect to type classes too, namely the _dictionary_. C.f. the `Monad` datatype which carries the `return`, `bind` and `fail` functionalities for monads.

# Details #

We give a very speculative account of how this could work by the example of a `Num` class that allows us to treat `Int` and `Float` by common terms.

```
prop Class :: Tag ~> a ~> *1 where
  Inst :: Instance nam a => {dictionary nam a} ~> Class nam a
```

Now we have to define Instance as prop too and hook up
the (plus, negate, mul, div) tuple to the mix.

Superclass constraints?

# How Haskell Classifies Type Classes #

A type class constraint (e.g. `Monad m`) is of kind `Constraint`. This functionality is available as of [GHC v7.4.1](http://www.haskell.org/ghc/docs/7.4.1/html/users_guide/constraint-kind.html) with the activated `ConstraintKinds` feature.

# Transfer to Ωmega #

We propose a family of kind (and higher) level classifiers `§n :: *(1+n)`. When `n` is 0 it can be omitted (similarly to the `*0 ≡ *` identity). We reuse the general `data` syntax to define type classes:

```
data Monad :: * ~> § where
  return :: a -> Monad a
  bind :: Monad a -> (a -> Monad b) -> Monad b
```

Simplified syntax is (and expands to the above):
```
class Monad a where
  return :: a -> Monad a
  bind :: Monad a -> (a -> Monad b) -> Monad b
```

Note that the type variable in `class Monad a` is not scoped.

We allow _constructor_ definitions in classes, these come handy when doing pattern matching over constrained types:
```
class Monoid a where
  One :: Monoid a
  mult :: Monoid a -> Monoid a -> Monoid a
```

Here is how this can be used:
```
isNeutral :: Monoid a => a -> Bool
isNeutral One = True;
isNeutral _ = False;
```

## Constraints that contribute to `Prop` ##

When the general syntax is used then the `class` keyword can be substituted by `prop`. In this case the constructors are checked for being valid reasoning rules, and in the case of success they are added to the set of truths.

## Instance definitions ##

Instances are declared with the `instance` keyword, just like in Haskell:
```
instance Monoid (List a) where
  One = []
  mult = append
```
Class constructors must be defined in terms of instance constructors.

But: It would be feasible to add a predicate in place of an actual constructor to implement _smart constructors_
```
instance Monoid (Smarty a) where
  One x = if ... x ...
  mult = ...
```

Or maybe class constructors could be pattern synonyms:

```
instance Monoid (Smarty a) where
  One = x | even x
  ...
```

When in term position `One 4` would be desugared as
```
case 4 of x | even x -> x
```


## Implementation details ##

Class constructors are added to the runtime dictionary for `§` as predicates on the value, i.e.
```
dict(Monoid).One :: Monoid a -> Bool
```
The pattern matching on class constructors boils down to the rewrite rule
```
foo One = ...
    ⇒
foo m | dict(Monoid).One m = ...
```

Logically, `dict(Monoid (List a)).One` is implemented just like `isNeutral` above.

Open issue: How can I implement type-level dictionaries (i.e. `§n` with n > 0)? Open type functions? Can narrowing be applied here at all?

# Aside: how `prop` would work under the new scheme #

The current proposition definition
```
prop Nat' :: Nat ~> * where
  Z :: Nat' Z
  S :: Nat' n -> Nat' (S n)
```
is adding a new data type (under `*0`) and a new proposition (under `§0 :: *1`) simultaneously, when possible.