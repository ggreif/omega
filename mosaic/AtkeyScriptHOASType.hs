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
  lam :: a t -> (a True -> a x) -> a False
  app :: a x -> a y -> a False
  failure :: a False
  have :: a True -> a ty -> a x -> a False
  hasType :: a ty -> a x -> a False
  -- Type section
  a :: a False
  b :: a False
  c :: a False
  arr :: a x -> a y -> a False
  unify :: a x -> a y -> a False

newtype TypeChecker' (g :: Bool) = TC (Maybe Type)
unTC (TC a) = a

instance Show (TypeChecker' v) where
  show = show . unTC

instance TypeChecker TypeChecker' where
  lam ty tcf = TC (do ty' <- unTC ty
                      tbody <- unTC (tcf $ TC (return ty'))
                      return $ ty' :-> tbody)

  app (TC cf) (TC ca) = TC (do ta :-> tr <- cf
                               ta' <- ca
                               guard $ ta == ta'
                               return tr)

  failure = TC $ Nothing

  have (TC v) (TC t) (TC tc) = TC (do ty' <- v
                                      ty <- t
                                      unTC $ TC (return ty) `unify` TC (return ty')
                                      tc)
  hasType (TC t) (TC tc) = TC (do ty' <- tc
                                  ty <- t
                                  unTC $ TC (return ty) `unify` TC (return ty')
                                  tc)
  a = TC $ return A
  b = TC $ return B
  c = TC $ return C
  TC (Just d) `arr` TC (Just c) = TC (return $ d :-> c)
  TC (Just l) `unify` TC (Just r) | l == r = TC (Just l)
  _ `unify` _ = failure


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
-}

t0, t1, t2, t3, t4, t5, t6 :: TypeChecker r => r False
t0 = lam a $ \x -> have x a x -- SUCCESS: a `arr` a
t1 = lam a $ \x -> have x b (app x x) -- FAIL (because of self-application)
t2 = lam a $ \x -> hasType a x -- SUCCESS: a `arr` a
t3 = lam (a `arr` b) $ \fun -> lam a $ \arg -> fun `app` arg -- SUCCESS
t4 = hasType ((a `arr` b) `arr` (a `arr` b)) t3 -- SUCCESS
t5 = hasType ((a `arr` a) `arr` (a `arr` b)) t3 -- FAIL (because of wrong assert)
t6 = lam a $ \x -> have x b x -- FAIL (because of wrong assert)


data Script :: Bool -> * where
  Var :: Script True
  Lam :: Script ty -> (Script True -> Script x) -> Script False
  App :: Script x -> Script y -> Script False
  Failure :: Script False
  Have :: Script True -> Script ty -> Script x -> Script False
  GoalIs :: Script ty -> Script x -> Script False
  Type :: Type -> Script False

instance TypeChecker Script where
  lam = Lam
  app = App
  failure = Failure
  have = Have
  hasType = GoalIs
  a = Type A; b = Type B; c = Type C
  Type d `arr` Type c = Type $ d :-> c

instance Show (Script b) where
  show Var = "VAR"
  show (Lam ty fb) = "Lam (" ++ show ty ++ ") (" ++ show (fb Var) ++ ")"
  show (f `App` a) = show f ++ "@" ++ show a
  show Failure = "Failure"
  show (Have v ty inn) = "Have " ++ show v ++ ":" ++ show ty ++ " in " ++ show inn
  show (GoalIs ty inn) = "GoalIs " ++ show ty ++ "     " ++ show inn
  show (Type ty) = show ty



-- #### (pre) bidirectional inferencer

newtype Bidir (v :: Bool) = BD (Type -> Type)
unBD (BD a) = a

instance TypeChecker Bidir where
  lam (BD ty) tcf = BD go
         where go want = ty undefined :-> tc undefined
               BD tc = tcf $ BD ty

  BD f `app` BD a = BD go
         where go want = resT
                 where argT' :-> resT = f (argT :-> want)
                       argT = a undefined

  failure = error "failing Bidir"

  hasType (BD ty) (BD tc) = BD go
         where go want = tc $ ty undefined

  have (BD v) ty (BD body) = (BD body) -- v ty -- FIXME!

  a = BD $ const A; b = BD $ const B; c = BD $ const C
  
  BD d `arr` BD c = BD $ const $ d undefined :-> c undefined

  BD l `unify` BD r = BD $ l . r
  



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

  a = BB $ known A; b = BB $ known B; c = BB $ known C
  lam (BB ty) tcf = BB go
         where go Univ = Ground $ obtain ty :-> obtain tc
               BB tc = tcf $ BB ty
               obtain t = case t Univ of Ground res -> res

  BB f `app` BB a = BB go
         where go (Ground want) = Ground resT
                 where Ground (argT' :-> resT) = f . Ground $ argT :-> want
                       Ground argT = a Univ

  failure = BB . const $ Contradiction "failure"
{-
  hasType ty (BB tc) = BB go
         where go want = tc ty

  have (BB v) ty (BB body) = (BB body) -- v ty -- FIXME!
-}
