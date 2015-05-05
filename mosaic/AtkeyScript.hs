-- this mosaic explores the way laid out by Robert Atkey in
--  http://bentnib.org/posts/2015-04-19-algebraic-approach-typechecking-and-elaboration.html

{-# LANGUAGE TypeOperators #-}

import Control.Monad

data Type = A | B | C | Type :-> Type deriving (Eq, Show)

infixr 9 :->

type TypeChecker = [Type] -> Maybe Type

-- a TypeChecker is basically something that maybe has a type in a context
--   (e.g. a Term)

var :: Int -> TypeChecker
var i = Just . (!!i)

lam :: Type -> TypeChecker -> TypeChecker
lam ty tc ctx = do tbody <- tc $ ty : ctx
                   return $ ty :-> tbody

app :: TypeChecker -> TypeChecker -> TypeChecker
app cf ca ctx = do (tf :-> ta) <- cf ctx
                   ta' <- ca ctx
                   guard $ ta == ta'
                   return ta

data Term = Var Int | Lam Type Term | Term `App` Term deriving Show

typeCheck :: Term -> TypeChecker
typeCheck (Var i) = var i
typeCheck (Lam ty tm) = lam ty $ typeCheck tm
typeCheck (f `App` a) = typeCheck f `app` typeCheck a
