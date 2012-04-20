This is an attempt to intercept and rewrite 'applications'
(that is juxtapositions of expressions) and change the
modus ponens typing rule to something more flexible.

Load this file with
 $ ghci -XTemplateHaskell ApplyRewriter.lhs

And then execute
 > $(dullness [| negate 1 |])



> {-# LANGUAGE TemplateHaskell #-}

> import Language.Haskell.TH
> import Control.Category
> import Prelude as P

> class Category c => Apply c where
>   (<$>) :: c a b -> a -> b

> instance Apply (->) where
>   (<$>) = ($)

> dullness :: ExpQ -> Q Exp
> dullness e = e >>= return P.. walkAST

> kk = (<$>) :: (a -> b) -> a -> b

> walkAST :: Exp -> Exp
> walkAST l@(LitE {}) = l
> walkAST (AppE f a) = AppE (AppE (VarE (mkName "kk")) f) a

