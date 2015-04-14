This is an attempt to intercept and rewrite 'applications'
(that is juxtapositions of expressions) and change the
modus ponens typing rule to something more flexible.

Load this file with
 $ ghci -XTemplateHaskell ApplyRewriter.lhs

And then execute
 > $$(dullness [|| negate 1 ||])



> {-# LANGUAGE TypeFamilies, TemplateHaskell, GADTs, KindSignatures,
>              TypeSynonymInstances, StandaloneDeriving,
>              MultiParamTypeClasses, FlexibleInstances #-}

> import Language.Haskell.TH
> import Control.Category
> import Prelude hiding ((.))
> import qualified Prelude ((.))
> import Language.Haskell.TH.Syntax
> -- import Data.Void

> data Void where

> class Category c => Apply c a b where
>   type Domain c a b :: *
>   type Codomain c a b :: *
>   type Domain c a b = a
>   type Codomain c a b = b
>   (<$>) :: c a b -> Domain c a b -> Codomain c a b
>   cry :: c (a, b) d -> c a (c b d)
>   ucr :: c a (c b d) -> c (a, b) d

> instance Apply (->) a b where
>   (<$>) = ($)
>   cry = curry
>   ucr = uncurry

> dullness :: Q (TExp a) -> Q (TExp Integer)
> dullness e = e >>= return . walkAST . unType

> walkAST :: Exp -> TExp Integer
> walkAST l@(LitE {}) = TExp l
> walkAST v@(VarE {}) = TExp v
> walkAST (AppE f a) = TExp a -- TExp $ VarE (mkName "<$>") `AppE` unType (walkAST f) `AppE` unType (walkAST a)

Now that we can perform the transformation, it would be interesting
to give a different instance.

> data LC :: * -> * -> * where
>   RAW :: Show a => a -> LC Void a
>   V :: LC Void Int
>   APP :: LC a b -> LC Void a -> LC Void b
>   ID :: LC a a
>   COMP :: LC b c -> LC a b -> LC a c
>   PLUS :: LC (Int, Int) Int
>   PAIR :: LC Void Int -> LC Void Int -> LC Void (Int, Int)
>   CURRY :: LC (a, b) d -> LC a (LC b d)
>   UNCURRY :: LC a (LC b d) -> LC (a, b) d

> deriving instance Show (LC a b)

> instance Category LC where
>   id = ID
>   (.) = COMP

We can do this now:
 > ID . ID

Try this now
 > $(dullness [| cid 1 |])

Alas, "cid 1" is typechecked before it gets passed to us :-(

Am I about to reimplement heterogenous metaprogramming?
See:
http://www.cs.berkeley.edu/~megacz/garrows/megacz-pop-talk.pdf

Anyway, can we try to conjure up an Apply instance?

> instance Apply LC a b where
>   type Domain LC a b = LC Void a
>   type Codomain LC a b = LC Void b
>   (<$>) = APP
>   cry = CURRY
>   ucr = UNCURRY


> -- instance Lift (LC' a b) where
> --   lift _ = [| negate |]


