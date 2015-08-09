# Introduction #

This is just the stripped down version of reflecting polynomial types to runtime (singleton) values.

Do dependent telescopes.

Convenient building with PHOAS or `sing`.


# Details #

## Products ##

We start with products.

Need these ingredients:
  * Name
  * Arity (implicit?)
  * Vector of fields, each with type-name and optionally with a name (possibly strictness?)

We use `Fin` values for accessing the fields
```
data Prod :: Symbol -> Nat -> [Symbol] -> * where
  Unit :: Sing (name :: Symbol) -> Prod name 0 '[]
  Field :: Prod name ary fs -> Sing (fty :: Symbol) -> Sing (fnm :: Maybe Symbol) -> Prod name (S ary) (fty ': fs)
```

For reference here is the Maybe kind:
```
data instance Sing (l :: Maybe k) where
  Nothing' :: Sing Nothing
  Just' :: Sing t -> Sing (Just t)

instance SingI (Nothing :: Maybe k) where
  sing = Nothing'
instance SingI (n :: k) => SingI (Just n :: Maybe k) where
  sing = Just' sing
```

## Sums ##


Need these ingredients:
  * Name
  * Vector of constructors, each with type-name and optionally with a name (possibly strictness?)


# PHOAS Builder #

# `sing` Builder #

# Termination #

For our DSL we probably do not want recursion in the data type.

# Questions #

Do we really want to refer to types and constructors by name or by LambdaGraph-like pointering?

Is `Typable` derivable?

Do we need a `(* -> *)` parameter for customization?

Are (partially) saturated lazy function calls just `Prod`ucts?

Is constructor selection just a type-level function called with constructor name (as well as type params/indices) returning a value-level function of appropriate arity?

Should we already add levels?

## The typeclass `Generic` ##

already produces type-level description of the structure of `data` definitions.