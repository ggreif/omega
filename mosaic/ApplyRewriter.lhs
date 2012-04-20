This is an attempt to intercept and rewrite 'applications'
(that is juxtapositions of expressions) and change the
modus ponens typing rule to something more flexible.

Load this file with
 $ ghci -XTemplateHaskell ApplyRewriter.lhs

And then execute
 > $(dullness [| 1 |])



> {-# LANGUAGE TemplateHaskell #-}

> import Language.Haskell.TH

> dullness :: ExpQ -> Q Exp
> dullness e = [| 1 |]

