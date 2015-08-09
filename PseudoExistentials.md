# Introduction #

Consider:
```
data Foo where Bar :: a -> Foo
```
There are no constraints on `a` whatsoever, so we can call `Bar` with any argument. OTOH when pattern-matching on `Bar` only the wildcard pattern `_` makes sense. So why store the argument at all?

# Details #

Similar observations exist when a is _weakly constrained_, i.e. there is a function or dictionary of functions attached to it which has `a` in contravariant position. Like this:
```
data Foo where Bar :: (a -> String) -> a -> Foo
```

The only way `a` can be used is to pass it to the function, but that produces a string thunk. Why not store the (lazy) string instead of the two arguments then? At the pattern site the two args are bound, but the function application can be rewritten to be the string thunk that is actually stored in the `Bar`.