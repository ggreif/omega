# Introduction #

Imagine that the programmer defines this:
```
data List a = Nil | Cons a (List a)

starts4 (Cons 4 _) = True
starts4 _ = False
```

The compiler would internally use a form of singleton types:
```
data List° :: List° a ~> * where
  °Nil :: List° a
  °Cons :: a ~> List° a ~> List° a

starts4 :: List° shape -> { Bool°: °True ~> List° (°Cons °4 rest); °False ~> List° unknown }
starts4 ...
```

So the return type would be enriched with the demanded shape of the argument(s).

We can also consider this a the _pattern matching is evidence creation_ principle. Some existential value that is passed as an argument gets scrutinized and proofs about the argument's structure created. These proofs precisely quantify the gain in information (i.e. loss of entropy).

# Details #

![Singleton-strictness.svg](https://github.com/ggreif/omega/blob/wiki/Singleton-strictness.svg)

The above image represents the dynamic value of the argument as passed to `starts4`. The opaque part is not demanded, the cloud represents a thunk (unevaluated value).

```
starts4 (Cons 4 $ Cons 2 $ something)
```

# Connection to _termination_ #

Both strictness and termination can hopefully be treated on equal grounds by tracking [_refinement coeffects_](https://github.com/ggreif/omega/blob/wiki/Coeffects.svg)
