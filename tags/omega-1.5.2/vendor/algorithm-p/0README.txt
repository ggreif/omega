Time-stamp: <2010-05-14 11:41:04 cklin>

Algorithm P for Plain GADT Type Inference
-----------------------------------------

  Chuan-kai Lin <cklin@cs.pdx.edu>
  Department of Computer Science
  Portland State University


This program implements Algorithm P, which infers types for GADT
programs that have no type annotations.  Algorithm P can infer types for
GADT programs whose pattern-matching branches have different types, and
it can infer types for GADT programs that use polymorphic recursion.  I
provide a detailed description of Algorithm P in my dissertation.

You can build an executable binary of the program using the Glasgow
Haskell Compiler (I use 6.12.1) with the following command:

  ghc --make -O3 Run

The build process generates an executable named Run (or Run.exe).  The
program reads its input from the file Examples.lhs and prints the type
inference result to the standard output.


The Examples.lhs file contains my test suite for the program.  The
Algorithm P implementation reads the test examples in the main part of
the file (it ignores literate Haskell code).  The file also contains
some literate Haskell programs (with type annotations), which you can
load directly into GHCi (which automatically ignores all the inputs to
the Algorithm P implementation as literate Haskell documentation).

