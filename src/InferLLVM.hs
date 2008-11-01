-- Copyright (c) Gabor Greif
-- email ggreif gmail com
-- Subject to conditions of distribution and use; see LICENSE.txt for details.

module InferLLVM() where

import Bind
import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import System.IO.Unsafe(unsafePerformIO)
import Monads
import Monad(when,foldM)

import RankN
import Syntax(Exp(..),Lit(..))


data LLType where
  LLInt :: LLType
  LLPtr :: LLType
  LLPair :: LLType -> LLType -> LLType
  LLTv :: TcTv -> LLType
 deriving (Show)


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

instance (TypeLike m LLType,TyCh m) => Typable m Lit LLType where
  check = checkLit
  infer = undefined -- :: term -> m (ty,term)

checkLit e@(Int _) LLInt = return e
checkLit e LLPtr = return e -- generic representation
checkLit e t = fail (show e ++ " does not check as " ++ show t)

instance (TypeLike m LLType,TyCh m) => Typable m Exp LLType where
  -- tc = undefined -- :: term -> Expected ty -> m term
  check = checkLL -- :: term -> ty -> m term
  infer = undefined -- :: term -> m (ty,term)

checkLL :: TyCh m => Exp -> LLType -> m Exp
checkLL e@(Lit l) t = do { _ <- check l t; return e }
checkLL e@(Prod e1 e2) (LLPair t1 t2) = do
                                        c1 <- checkLL e1 t1
                                        c2 <- checkLL e2 t2
                                        return (Prod c1 c2)
