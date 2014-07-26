{-# LANGUAGE DataKinds, KindSignatures, TypeOperators
           , PolyKinds, GADTs, MultiParamTypeClasses
           , FlexibleContexts, ScopedTypeVariables
           , RebindableSyntax #-}


import GHC.TypeLits
import Data.Proxy
import Data.String

data Size s where Size :: KnownNat s => Size s
data Name n where Name :: KnownSymbol n => Name n

data L = Done | Symbol `Reg` Nat | L `Then` L | Origin Nat
infixr 1 `Then`
infixr 2 `Reg`

class Layout (proxy :: L -> *) where
  base :: KnownNat o => proxy (Origin o)
  reg :: (KnownSymbol n, KnownNat s) => proxy (n `Reg` s)
  return :: a -> proxy Done
  (>>) :: proxy l -> proxy l' ->  proxy (l `Then` l')
  (>>=) :: proxy l -> (proxy l -> proxy l') -> proxy (l `Then` l')
  fail :: String -> proxy a

t1 :: Layout Proxy => Proxy (Origin 42 `Then` "FOO" `Reg` 4 `Then` "BAR" `Reg` 4 `Then` Done)
t1 = do base :: Proxy (Origin 42)
        reg :: Proxy ("FOO" `Reg` 4)
        reg :: Proxy ("BAR" `Reg` 4)
        return ()

instance Layout Proxy