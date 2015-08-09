Conceived and implemented by Tim Sheard and his students, Ωmega is a cross between a purely functional programming language and a theorem prover. The syntax is borrowed from Haskell and has been moderately extended.

## Ωmega offers these features: ##

  * default strict evaluation
  * laziness on demand
  * type-level functions
  * kind system with user-definable kinds at any level
  * level polymorphism
  * theorems can be formulated as types and proven with values (Curry-Howard Correspondence)
  * GADT syntax for datatypes
  * singleton types (emulating dependent types)
  * custom syntax for recurring datatype patterns
  * metaprogramming facilities
    1. staging constructs
    1. freshness

## Non-features (yet) ##

  * termination of the logic fragment
  * type classes (ad-hoc polymorphism)
  * compiled binaries
  * efficient execution
  * debugging

## Anti-features ##

  * proper dependent types (will never happen)