-- this mosaic explores the way laid out by Robert Atkey in
--  http://bentnib.org/posts/2015-04-19-algebraic-approach-typechecking-and-elaboration.html

-- The Algebraic Theory of Typechecking
--  around slide 30
--   (for previous slides consult revision history)

{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, TypeOperators #-}

import Control.Monad

data Type = A | B | C | Type :-> Type deriving (Eq, Show)

infixr 9 :->

type TypeChecker' = [Type] -> Maybe Type

-- a TypeChecker is basically something that maybe has a type in a context
--   (e.g. corresponding to a Term)

class TypeChecker a where

  var :: Int -> a
-- var i = return . (!!i)

  lam :: Type -> a -> a
-- lam ty tc ctx = do tbody <- tc $ ty : ctx
--                    return $ ty :-> tbody

  app :: a -> a -> a
--app cf ca ctx = do (ta :-> tr) <- cf ctx
--                   ta' <- ca ctx
--                   guard $ ta == ta'
--                   return tr

  failure :: a
  have :: Int -> Type -> a -> a
  hasType :: Type -> a -> a

instance TypeChecker TypeChecker' where
  var i = return . (!!i)

  lam ty tc ctx = do tbody <- tc $ ty : ctx
                     return $ ty :-> tbody

  app cf ca ctx = do (ta :-> tr) <- cf ctx
                     ta' <- ca ctx
                     guard $ ta == ta'
                     return tr


data Term = Var Int | Lam Type Term | Term `App` Term deriving Show

typeCheck :: Term -> TypeChecker'
typeCheck (Var i) = var i
typeCheck (Lam ty tm) = lam ty $ typeCheck tm
typeCheck (f `App` a) = typeCheck f `app` typeCheck a


-- More bits
failure' :: TypeChecker'
failure' = const Nothing

have' :: Int -> Type -> TypeChecker' -> TypeChecker'
have' i ty tc ctx = do ty' <- var i ctx
                       guard $ ty == ty'
                       tc ctx

hasType' :: Type -> TypeChecker' -> TypeChecker'
hasType' ty tc ctx = do ty' <- tc ctx
                        guard $ ty == ty'
                        return ty
