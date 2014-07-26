{-# LANGUAGE DataKinds, KindSignatures, TypeOperators
           , PolyKinds, GADTs, MultiParamTypeClasses
           , FlexibleContexts, ScopedTypeVariables
           , RebindableSyntax #-}


import GHC.TypeLits
import Data.Proxy
import Data.String

data Size s where Size :: KnownNat s => Size s
data Name n where Name :: KnownSymbol n => Name n

data L = Symbol `Reg` Nat | L `After` L

class {-Monad m => -}Layout m (proxy :: L -> *) where
  reg :: Name n -> Size s -> m (proxy (n `Reg` s))
  reg' :: (KnownSymbol n, KnownNat s) => m (proxy (n `Reg` s))
  return :: a -> m a
  (>>) :: m (proxy l) -> m (proxy l') ->  m (proxy (l `After` l'))
  (>>=) :: m (proxy l) -> (proxy l -> m (proxy l')) ->  m (proxy (l `After` l'))
  fail :: String -> m a

t1 :: Layout m Proxy => m (Proxy ("FOO" `Reg` 4), Proxy ("BAR" `Reg` 4))
t1 = do lens1 <- reg' :: m (Proxy ("FOO" `Reg` 4))
        lens2 <- reg' :: m (Proxy ("BAR" `Reg` 4))
        return (lens1, lens2)

--instance Map