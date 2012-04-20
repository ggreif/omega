This is an attempt to intercept and rewrite 'applications'
(that is juxtapositions of expressions) and change the
modus ponens typing rule to something more flexible.

Load this file with
 $ ghci -XTemplateHaskell ApplyRewriter.lhs

And then execute
 > $(dullness [| negate 1 |])



> {-# LANGUAGE TemplateHaskell, GADTs, KindSignatures,
>              TypeSynonymInstances, StandaloneDeriving #-}

> import Language.Haskell.TH
> import Control.Category
> import Prelude hiding ((.))
> import qualified Prelude ((.))

> class Category c => Apply c where
>   (<$>) :: c a b -> a -> b

> instance Apply (->) where
>   (<$>) = ($)

> dullness :: ExpQ -> Q Exp
> dullness e = e >>= return Prelude.. walkAST

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

> deriving instance Show (LC a)

> newtype LC' a b = CLC (LC (a -> b)) deriving Show

> instance Category LC' where
>   id = CLC ID
>   CLC a . CLC b = CLC (a `COMP` b)

We can do this now:
 > CLC ID Control.Category.. CLC ID

> cid = CLC ID

Try this now
 > $(dullness [| cid 1 |])

Alas, "cid 1" is typechecked before it gets passed to us :-(
