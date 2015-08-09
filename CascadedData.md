# Introduction #

Here is a typical GADT-style `data` declaration:
```
data Bool :: * where
  False :: Bool
  True :: Bool
```
I.e. three levels appear connected by typing annotation `False :: Bool :: *`. Pretty boring.

However, even dependently typed languages don't allow (nontrivial) connection of more levels.

For Ωmega2, I'd like to allow cascaded `data` declarations.

# Cascaded `data` Declarations #

For eventual higher kind `*1` (or higher) one could declare
```
data Baz :: *1 ~> *1 where
    data Bar :: *0 ~> Baz *0 where
        Foo :: Bar Int
        Quux :: a ~> Bar a
    Howdy :: Baz b
```

This way we would get a user-defined four-level construct `Foo :: Bar Int :: Baz *0 :: *1`. Consequently `Foo`, as well as `Quux`, lives on the value (i.e. runtime) level.

Naturally, as I nest `data` declarations deeper and deeper I have to start at even higher kinds, as no definition can descend lower than the level of values.

# Why? #

I can only imagine, that longer nontrivial typing chains allow us to model invariants even more precisely, giving the type-checker even more power.

I can only draw the analogy to homology theories, where short exact sequences describe something simple, but longer exact sequences also exist and characterize fancier spaces.

Can these be artifacts of _alien_ (i.e. non-`Hask`) categories?