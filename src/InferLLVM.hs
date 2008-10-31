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
  LLTv :: TcTv -> LLType


instance (HasIORef m,Fresh m) => Zonk m LLType where
 zonkG = zonkLL
 tvs = tvs_LL


zonkLL :: (HasIORef m,Fresh m) => LLType -> m LLType
zonkLL a@LLInt = return a
zonkLL a@LLPtr = return a
zonkLL (LLPair x y) = binaryLift pair (zonkLL x) (zonkLL y)
zonkLL (LLTv (Tv un flav k)) = do { k2 <- zonkKind k; return (LLTv (Tv un flav k2)) }

pair :: LLType -> LLType -> LLType
pair x y = LLPair x y

tvs_LL :: (HasIORef m,Fresh m) => LLType -> m([TcTv],[TcLv])
tvs_LL LLInt = return ([], [])
tvs_LL LLPtr = return ([], [])
tvs_LL (LLPair x y) = binaryLift unionP (tvs_LL x) (tvs_LL y)
--tvs_LL (LLTv v) = tvs v

instance TyCh m => TypeLike m LLType where
  sub = undefined


instance (TypeLike m LLType,TyCh m) => Typable m Exp LLType where
  tc = undefined -- :: term -> Expected ty -> m term
  check = undefined -- :: term -> ty -> m term
  infer = undefined -- :: term -> m (ty,term)

