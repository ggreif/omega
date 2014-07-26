{-# LANGUAGE DataKinds, KindSignatures, TypeOperators
           , PolyKinds, GADTs, MultiParamTypeClasses
           , FlexibleContexts, ScopedTypeVariables #-}


import GHC.TypeLits
import Data.Proxy

data Size s where Size :: KnownNat s => Size s
data Name n where Name :: KnownSymbol n => Name n
--type Name = KnownSymbol

data L = Symbol `Reg` Nat

class Monad m => Layout m (proxy :: L -> *) where
  reg :: Name n -> Size s -> m (proxy (n `Reg` s))
  reg' :: (KnownSymbol n, KnownNat s) => m (proxy (n `Reg` s))

t1 :: Layout m Proxy => m (Proxy ("FOO" `Reg` 4), Proxy ("BAR" `Reg` 4))
t1 = do lens1 <- reg' :: m (Proxy ("FOO" `Reg` 4))
        lens2 <- reg' :: m (Proxy ("BAR" `Reg` 4))
        return (lens1, lens2)

--instance Map