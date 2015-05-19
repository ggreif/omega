-- this mosaic explores the way laid out by Robert Atkey in
--  http://bentnib.org/posts/2015-04-19-algebraic-approach-typechecking-and-elaboration.html

-- The Algebraic Theory of Typechecking
--  around slide 30
--   (for previous slides consult revision history)

{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, TypeOperators
           , KindSignatures #-}

import Control.Monad

data Type = A | B | C | Type :-> Type deriving (Eq, Show)

infixr 9 :->

--type TypeChecker' g = [Type] -> Maybe Type

-- a TypeChecker is basically something that maybe has a type in a context
--   (e.g. corresponding to a Term)

class TypeChecker (a :: Bool -> *) where
  --var :: Int -> a
  lam :: Type -> (a True -> a x) -> a False
  app :: a x -> a y -> a False
  failure :: a False
  have :: a True -> Type -> a x -> a False
  hasType :: Type -> a x -> a False

--instance TypeChecker TypeChecker' where
  --var i = return . (!!i)
{-
  lam ty tc ctx = do tbody <- tc $ ty : ctx
                     return $ ty :-> tbody

  app cf ca ctx = do (ta :-> tr) <- cf ctx
                     ta' <- ca ctx
                     guard $ ta == ta'
                     return tr

  failure = const Nothing
  have i ty tc ctx = do ty' <- var i ctx
                        guard $ ty == ty'
                        tc ctx
  hasType ty tc ctx = do ty' <- tc ctx
                         guard $ ty == ty'
                         return ty
-}

{-
data Term a = Var | Lam Type (Term a -> Term a) | Term a `App` Term a deriving Show


typeCheck :: Term -> TypeChecker'
--typeCheck (Var i) = var i
typeCheck (Lam ty f) = lam ty $ typeCheck (f Var)
typeCheck (f `App` a) = typeCheck f `app` typeCheck a
-}

t1 :: TypeChecker r => r False
t1 = lam A $ \x -> have x B (app x x)