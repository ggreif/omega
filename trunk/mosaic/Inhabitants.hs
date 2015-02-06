{-# LANGUAGE RebindableSyntax #-}

import qualified Prelude as P


data Lam = App Lam Lam | Inh (Lam -> Lam)



(>>=) :: () -> (Lam -> Lam) -> Lam
(>>=) () = Inh

return a = a
fail = P.error

main' = do i <- ()
           i
           