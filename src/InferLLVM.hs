module InferLLVM where

import Bind
import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import System.IO.Unsafe(unsafePerformIO)
import Monads
import Monad(when,foldM)

import RankN
import Syntax(Exp(..))


data LLType where
  LLInt :: LLType
  LLPtr :: LLType
  LLPair :: LLType -> LLType -> LLType


instance (HasIORef m,Fresh m) => Zonk m LLType where
 zonkG = zonkLL
 tvs = undefined


zonkLL:: (HasIORef m,Fresh m) => LLType -> m LLType
--zonkLL (Rarrow x y) = binaryLift arrow (zonkSigma x) (zonkRho y)
zonkLL (LLPair x y) = binaryLift pair (zonkLL x) (zonkLL y)
--zonkLL (Rsum x y) = binaryLift rsum (zonkSigma x) (zonkSigma y)
--zonkLL (Rtau x) = do { w <- zonkTau x; return(Rtau w)}
pair :: LLType -> LLType -> LLType
pair x y = LLPair x y


instance TyCh m => TypeLike m LLType where
  sub = undefined
