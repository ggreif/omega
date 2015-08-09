# Introduction #

CCs are not types but constraints on them! See also the reversed direction [types are calling conventions](http://lambda-the-ultimate.org/node/3319).

e.g. `'[Int :> R3, Bool :> CR0, Push Int, Push Bool, Bool :> R4!3, Word8 :> R4!!(8,16)] :: [Loc arch]`

It must satisfy the Constraint
```
class MachModel arch => CallingConv [Loc arch] where
  -- extract values codegen
  -- calculate (stack) area
  -- etc.
```

## `Loc` can be ##

  * `Push` for passing data on the stack
  * `Pop` for receiving results from the stack
  * `(:>)` and `(:<)` for passing and returning in registers
  * `Cont` for multiple returns (continuations)
  * `Preserve` for declaring invariants

These are typed locations

(Should we model the PC, program counter?)

## The types ##

come from an architecture-specific universe (`PPC`, `PPC64`, `PPC64le`, `x86`, `ARM`, etc.)

Haskell types map to these, and strictness is reflected in the types.

Metainformation is reflected in the types too. I.e. waymarked lists live in (linearly used while buildup) chunks, tagspace is either the values, or when unboxed or exhausted tagspace then in the first word of the chunk.

## The registers ##

These are architecture-specific too. Support for bit-slicing.