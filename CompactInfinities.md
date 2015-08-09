# Introduction #

Infinitary lambda calculus.

Finitely represented by graphs.

Graph unification. PHOAS graph representation.

`mdo` graph building.


# Details #

if I have a constructor
```
Next :: forall a :: Nat . T a -> T a (S a)
```

then I'd like to build the infinite ascent like this:
```
asc :: T 1 {fix S}
asc = Next 1 asc
```
For this we need a unification algorithm that allows an (open) index interval in certain places.

With rigid unification `asc` would not typecheck, as the `1` has a very concrete type which taints it.

I do not want to use `unsafeCoerce` to construct a stream over an indexed data type.