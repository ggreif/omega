# Introduction #


Löb's theorem

See [Piponi](http://blog.sigfpe.com/2006/11/from-l-theorem-to-spreadsheet.html), [quchen(github)](https://github.com/quchen/articles/blob/master/loeb-moeb.md)

Video about spreadsheet eval (Boston?)
Kenneth Foner: http://youtu.be/F7F-BzOB670

Recursive types. Linking.

  * Möb, a generalisation: http://www.reddit.com/r/haskell/comments/1qwjk6/löb_and_möb_strange_loops_in_haskell/
  * Effectful: http://www.reddit.com/r/haskell/comments/1rgvr5/effectful_loeb/


# Details #



Box and partial evaluation ("known"). Applying a known function to a known argument gives us a known result.
http://ropas.snu.ac.kr/~jwchoi/talks/snt111118.pdf

`□(Int → Int) → □Int → □Int` works like this:
(1+) 5 → 6
Some calculations can run at compile time. _Note that we do need to know the innards of `(1+)` to be able to run it._

This is the essence of an applicative functor: `□(Int → Int) → □Int → □Int`

Löb is `□(□a → a) → □a`