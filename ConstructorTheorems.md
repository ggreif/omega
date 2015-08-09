# Introduction #

An unusual approach to retrofit constructors with type-level rules.

Consider the length function
```
length [] = 0
length (a:as) = 1 + length as
```
This is a catamorphism and has the type `length :: [a] -> Int`. But what if we want `Nat' a` as the range? And we also want (gasp!) a correctness guarantee?

The idea is to locally augment the constructors with _theorems_:
```
let theorem (:) :: a -> Nat' n -> Nat' (1+n)t
    theorem [] :: Nat' 0t
```
And then proceed defining:
```
lengthNat [] = 0v
lengthNat (a:as) = (1+lengthNat as)v
```

# Details #

Several points to consider:
  * Any type coming from the theorems needs to be hidden existentially.
  * Can these automatically be packed? Or do we need another mechanism?
  * Occulted type transformers on constructors that are locally refined?
  * How can we make this more catamorphism-like?
  * `S^0` is `id` on `Nat`
  * Can we _forget_ `Nat' n` to a (value-level) `Nat`?

Okay, how can the rules be attached to constructors? How can the rules access the type parameters?
```
(:) :: a -> [a] -> [a]
```
This is the default theorem. We can establish a local one
```
theorem (:) :: a -> (b, bs) -> (a, (b, bs))
```
which would create some signature of a _generalized fold_.

In a sense what we are doing here is retrofitting some `prop` definition on a previously defined data type. This syntax may be useful
```
let prop [a] where
  [] :: ...
  (:) :: ...
```

## The problem of existentials ##

Of course I've been vague about the type of `lengthNat` above. As you cannot pull out fresh universals of your hat, these must be _packed existentially_. So the signature would become
```
lengthNat :: [a] -> exists a . Nat' a
```
But this means tedious packing and unpacking each time. To automatize this part (and help the typechecker, which cannot see through `Ex`), I propose
```
... where exists theorem (:) :: a -> Nat' n -> Nat' (1+n)t
```
It may well turn out that _all_ interesting cases of constructor theorems need the existential wrapping feature, in which case we can drop the `exists`.

# Related Work #

This idea is very much influenced by Conor's [ornament cycle of papers](https://personal.cis.strath.ac.uk/conor.mcbride/pub/OAAO/Ornament.pdf). The above example (in the intro) is very similar to the [R\* talk](http://sneezy.cs.nott.ac.uk/fun/nov-07/R-star.pdf).

Generalized folds go back to "Generalised folds for nested datatypes" by Bird and Paterson.

This may be relevant too: http://comonad.com/reader/2009/incremental-folds/.