This is an attempt to intercept and rewrite 'applications'
(that is juxtapositions of expressions) and change the
modus ponens typing rule to something more flexible.

> {-# LANGUAGE TemplateHaskell #-}

> import Language.Haskell.TH

> dullness :: Exp -> Q Exp
> dullness e = [| 1 |]
