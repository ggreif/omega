-- this mosaic explores the way laid out by Robert Atkey in
--  http://bentnib.org/posts/2015-04-19-algebraic-approach-typechecking-and-elaboration.html

-- The Algebraic Theory of Typechecking
--  around slide 30
--   (for previous slides consult revision history)

{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, TypeOperators
           , KindSignatures, GADTs, DataKinds #-}

import Control.Monad

data Type = A | B | C | Type :-> Type deriving (Eq, Show)

infixr 9 :->


-- a TypeChecker is basically something that maybe has a type in a context
--   (e.g. corresponding to a Term)

class TypeChecker (a :: Bool -> *) where
  lam :: Type -> (a True -> a x) -> a False
  app :: a x -> a y -> a False
  failure :: a False
  have :: a True -> Type -> a x -> a False
  hasType :: Type -> a x -> a False

newtype TypeChecker' (g :: Bool) = TC ([Type] -> Maybe Type)
unTC (TC a) = a

instance TypeChecker TypeChecker' where
  lam ty tcf = TC (\ctx -> do tbody <- unTC (tcf $ TC (return . const ty)) (ty : ctx)
                              return $ ty :-> tbody)

  app (TC cf) (TC ca) = TC (\ctx -> do (ta :-> tr) <- cf ctx
                                       ta' <- ca ctx
                                       guard $ ta == ta'
                                       return tr)

  failure = TC $ const Nothing
  have (TC v) ty (TC tc) = TC (\ctx -> do ty' <- v ctx
                                          guard $ ty == ty'
                                          tc ctx)
  hasType ty (TC tc) = TC (\ctx -> do ty' <- tc ctx
                                      guard $ ty == ty'
                                      return ty)


data Term :: (Bool -> *) -> Bool -> * where
  Var' :: r True -> Term r True
  Lam' :: Type -> (Term r True -> Term r a) -> Term r False
  App' :: Term r a -> Term r b -> Term r False

--deriving Show


typeCheck :: TypeChecker r => Term r b -> r b
typeCheck (Var' v) = v
typeCheck (Lam' ty f) = lam ty $ \v -> typeCheck (f $ Var' v)
typeCheck (f `App'` a) = typeCheck f `app` typeCheck a


t1 :: TypeChecker r => r False
t1 = lam A $ \x -> have x B (app x x)

data Script :: Bool -> * where
  Var :: Script True
  Lam :: Type -> (Script True -> Script x) -> Script False
  App :: Script x -> Script y -> Script False
  Failure :: Script False
  Have :: Script True -> Type -> Script x -> Script False
  GoalIs :: Type -> Script x -> Script False

instance TypeChecker Script where
  lam = Lam
  app = App
  failure = Failure
  have = Have
  hasType = GoalIs


instance Show (Script b) where
  show Var = "VAR"
  show (Lam ty fb) = "Lam (" ++ show ty ++ ") (" ++ show (fb Var) ++ ")"
  show (f `App` a) = show f ++ "@" ++ show a
  show Failure = "Failure"
  show (Have v ty inn) = "Have " ++ show v ++ ":" ++ show ty ++ " in " ++ show inn
  show (GoalIs ty inn) = "GoalIs " ++ show ty ++ "     " ++ show inn
