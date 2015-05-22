-- this mosaic explores the way laid out by Robert Atkey in
--  http://bentnib.org/posts/2015-04-19-algebraic-approach-typechecking-and-elaboration.html

-- The Algebraic Theory of Typechecking
--  around slide 30
--   (for previous slides consult revision history)

{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, TypeOperators
           , KindSignatures, GADTs, DataKinds, StandaloneDeriving
           , ViewPatterns #-}

import Control.Monad

-- a TypeChecker is basically something that maybe has a type in a context
--   (e.g. corresponding to a Term)

class TypeChecker (a :: Bool -> *) where
  lam :: Type -> (a True -> a x) -> a False
  app :: a x -> a y -> a False
  failure :: a False
  have :: a True -> Type -> a x -> a False
  hasType :: Type -> a x -> a False
  -- Type section
  a :: a False
  b :: a False
  c :: a False
  arr :: a x -> a y -> a False
  -- unify :: a x -> a y -> a False

newtype TypeChecker' (g :: Bool) = TC (Maybe Type)
unTC (TC a) = a

instance Show (TypeChecker' v) where
  show = show . unTC

instance TypeChecker TypeChecker' where
  lam ty tcf = TC (do tbody <- unTC (tcf $ TC (return ty))
                      return $ ty :-> tbody)

  app (TC cf) (TC ca) = TC (do ta :-> tr <- cf
                               ta' <- ca
                               guard $ ta == ta'
                               return tr)

  failure = TC $ Nothing

  have (TC v) ty (TC tc) = TC (do ty' <- v
                                  guard $ ty == ty'
                                  tc)
  hasType ty (TC tc) = TC (do ty' <- tc
                              guard $ ty == ty'
                              return ty)

data Type = A | B | C | Type :-> Type deriving (Eq, Show)

infixr 9 :->

{-
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


-- #### (pre) bidirectional inferencer

newtype Bidir (v :: Bool) = BD (Type -> Type)
unBD (BD a) = a

instance TypeChecker Bidir where
  lam ty tcf = BD go
         where go want = ty :-> tc undefined
               BD tc = tcf $ BD (const ty)

  BD f `app` BD a = BD go
         where go want = resT
                 where argT' :-> resT = f (argT :-> want)
                       argT = a undefined

  failure = error "failing Bidir"

  hasType ty (BD tc) = BD go
         where go want = tc ty

  have (BD v) ty (BD body) = (BD body) -- v ty -- FIXME!



data Type' where
  Univ :: Type'
  Ground :: Type -> Type'
  Contradiction :: String -> Type'

deriving instance Show Type'

newtype BidirBetter (v :: Bool) = BB (Type' -> Type')
unBB (BB a) = a

known :: Type -> Type' -> Type'
known _ c@Contradiction{} = c
known ty Univ = Ground ty
known ty g@(Ground ty') | ty == ty' = g
known ty (Ground ty') = Contradiction $ show ty ++ " /= " ++ show ty'


instance TypeChecker BidirBetter where
  lam ty tcf = BB go
         where go Univ = Ground $ ty :-> (case tc Univ of Ground res -> res)
               BB tc = tcf $ BB (known ty)
-}
{-
  BB f `app` BB a = BB go
         where go want = resT
                 where argT' :-> resT = f (argT :-> want)
                       argT = a undefined

  failure = error "failing Bidir"

  hasType ty (BB tc) = BB go
         where go want = tc ty

  have (BB v) ty (BB body) = (BB body) -- v ty -- FIXME!
-}
