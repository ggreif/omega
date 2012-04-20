This is an attempt to intercept and rewrite 'applications'
(that is juxtapositions of expressions) and change the
modus ponens typing rule to something more flexible.

Load this file with
 $ ghci -XTemplateHaskell ApplyRewriter.lhs

And then execute
 > $(dullness [| negate 1 |])



> {-# LANGUAGE TemplateHaskell, GADTs, KindSignatures,
>              TypeSynonymInstances #-}

> import Language.Haskell.TH
> import Control.Category
> import Prelude as P

> class Category c => Apply c where
>   (<$>) :: c a b -> a -> b

> instance Apply (->) where
>   (<$>) = ($)

> dullness :: ExpQ -> Q Exp
> dullness e = e >>= return P.. walkAST

> walkAST :: Exp -> Exp
> walkAST l@(LitE {}) = l
> walkAST v@(VarE {}) = v
> walkAST (AppE f a) = AppE (AppE (VarE (mkName "<$>")) (walkAST f)) (walkAST a)

Now that we can perform the transformation, it would be interesting
to give a different instance.

> data LC :: * -> * where
>   V :: LC Int
>   APP :: LC (a -> b) -> LC a -> LC b
>   ID :: LC (a -> a)
>   COMP :: LC (b -> c) -> LC (a -> b) -> LC (a -> c)

> newtype LC' a b = CLC (LC (a -> b))

> instance Category LC' where
>   id = CLC ID
>   CLC a . CLC b = CLC (a `COMP` b)
