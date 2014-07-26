{-# LANGUAGE DataKinds, KindSignatures, TypeOperators
           , PolyKinds, GADTs, MultiParamTypeClasses
           , FlexibleContexts, ScopedTypeVariables
           , RebindableSyntax #-}


import GHC.TypeLits
import Data.Proxy
import Data.String

data Size s where Size :: KnownNat s => Size s
data Name n where Name :: KnownSymbol n => Name n

data L = Done | Symbol `Reg` Nat | L `After` L
infixr 1 `After`
infixr 2 `Reg`

class Layout (proxy :: L -> *) where
  reg :: Name n -> Size s -> proxy (n `Reg` s)
  reg' :: (KnownSymbol n, KnownNat s) => proxy (n `Reg` s)
  return :: a -> proxy Done
  (>>) :: proxy l -> proxy l' ->  proxy (l `After` l')
  (>>=) :: proxy l -> (proxy l -> proxy l') -> proxy (l `After` l')
  fail :: String -> proxy a

t1 :: Layout Proxy => Proxy (("FOO" `Reg` 4) `After` ("BAR" `Reg` 4) `After` Done)
--t1 :: Layout Proxy => Proxy Lens
t1 = do {-lens1 <- -}reg' :: Proxy ("FOO" `Reg` 4)
        {-lens2 <- -}reg' :: Proxy ("BAR" `Reg` 4)
                     return () -- return (lens1, lens2)

--instance Map