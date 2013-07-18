{-# LANGUAGE KindSignatures, DataKinds, TypeOperators, StandaloneDeriving, GADTs,
             MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
             UndecidableInstances, TypeHoles, TypeFamilies #-}

-- See: https://code.google.com/p/omega/wiki/LambdaGraph
-- TODO: model "let(rec) a = sub in expr" with KILL1 @ sub (expr ... UP LEFT)
-- TODO: LEFT of LAMBDA
-- TODO: HERE = UP STOP
-- TODO: class Typed where itsType :: l sh -> levup l sh
-- TODO: a simple minded interpreter (abstracted monadic?), compiler?

data {-kind-} Lam = App Lam Lam | Abs Lam | Ref [Go]
data {-kind-} Go = Up | Le | Ri | Down

data {-kind-} Trace = Root Lam | AppL Trace Lam | AppR Trace Lam | AbsD Trace Lam

-- a zipper for lambda trees
--
data Traced :: (Lam -> *) -> Trace -> * where
  EmptyRoot :: Builder l => l sh -> Traced l (Root sh)
  AppLeft :: (Shape tr ~ App shl shr, Builder l) => Traced l tr -> l (App shl shr) -> Traced l (AppL tr shl)
  AppRight :: (Shape tr ~ App shl shr, Builder l) => Traced l tr -> l (App shl shr) -> Traced l (AppR tr shr)
  AbsDown :: (Shape tr ~ Abs sh, Builder l) => Traced l tr -> l (Abs sh) -> Traced l (AbsD tr sh)

deriving instance Show (Traced Classical tr)

class Builder (shape :: Lam -> *) where
  lam :: shape inner -> shape (Abs inner)
  app :: shape left -> shape right -> shape (App left right)
  here :: shape (Ref '[Up])
  up :: shape (Ref p) -> shape (Ref (Up ': p))
  close :: Closed sh env => Traced shape env -> shape sh -> shape sh
  close _ sh = sh
  checkClosure :: (Shape env ~ sh) => Traced shape env -> shape sh -> Maybe (Proven sh env)

class Closed (sh :: Lam) (env :: Trace)
instance Closed (Ref '[]) env
instance Closed (Ref more) up => Closed (Ref (Up ': more)) ((down :: Trace -> Lam -> Trace) up sh)

type family Shape (env :: Trace) :: Lam
type instance Shape (Root sh) = sh
type instance Shape ((down :: Trace -> Lam -> Trace) up sh) = sh

instance CanGo (Le ': more) (Shape env) => Closed (Ref (Le ': more)) env
instance CanGo (Ri ': more) (Shape env) => Closed (Ref (Ri ': more)) env
instance CanGo (Down ': more) (Shape env) => Closed (Ref (Down ': more)) env

class CanGo (down :: [Go]) (from :: Lam)
instance CanGo '[] sh
instance CanGo more l => CanGo (Le ': more) (App l r)
instance CanGo more r => CanGo (Ri ': more) (App l r)
instance CanGo more d => CanGo (Down ': more) (Abs d)


instance Closed below (AbsD env below) => Closed (Abs below) env
instance (Closed left (AppL env left), Closed right (AppR env right)) => Closed (App left right) env

data Proven :: Lam -> Trace -> * where
  TrivialRef :: Proven (Ref '[]) env
  ProvenRefUp :: Closed (Ref more) env => Proven (Ref more) env -> Proven (Ref (Up ': more)) ((down :: Trace -> Lam -> Trace) env stuff)
  ProvenRefLeft :: (CanGo more (Shape (AppL env l)), Shape env ~ App l r) => Proven (Ref more) (AppL env l) -> Proven (Ref (Le ': more)) env
  ProvenRefRight :: (CanGo more (Shape (AppR env r)), Shape env ~ App l r) => Proven (Ref more) (AppR env r) -> Proven (Ref (Ri ': more)) env
  ProvenRefDown :: (CanGo more (Shape (AbsD env d)), Shape env ~ Abs d) => Proven (Ref more) (AbsD env d) -> Proven (Ref (Down ': more)) env
  ProvenApp :: (Closed l (AppL env l), Closed r (AppR env r)) =>
               Proven l (AppL env l) -> Proven r (AppR env r) ->
               Proven (App l r) env
  ProvenAbs :: Closed below (AbsD env below) =>
               Proven below (AbsD env below) -> Proven (Abs below) env

deriving instance Show (Proven sh env)

data SameShape :: (Lam -> *) -> Trace -> * where
  Lefty :: (AppLShape env ~ AppL env sh) => Traced l (AppLShape env) -> SameShape l env
  Righty :: (AppRShape env ~ AppR env sh) => Traced l (AppRShape env) -> SameShape l env
  Downy :: (AbsDShape env ~ AbsD env sh) => Traced l (AbsDShape env) -> SameShape l env


type family AppLShape (env :: Trace) :: Trace
type instance AppLShape (Root (App l r)) = AppL (Root (App l r)) l
type instance AppLShape ((down :: Trace -> Lam -> Trace) up (App l r)) = AppL (down up (App l r)) l

relevantLeft :: Traced Classical env -> Maybe (SameShape Classical env)
relevantLeft env@(EmptyRoot a@(APP _ _)) = return $ Lefty (AppLeft env a)
relevantLeft env@(AbsDown _ (LAM a@(APP _ _))) = return $ Lefty (AppLeft env a)
relevantLeft env@(AppLeft _ (APP a@(APP _ _) _)) = return $ Lefty (AppLeft env a)
relevantLeft env@(AppRight _ (APP _ a@(APP _ _))) = return $ Lefty (AppLeft env a)
relevantLeft _ = Nothing

type family AppRShape (env :: Trace) :: Trace
type instance AppRShape (Root (App l r)) = AppR (Root (App l r)) r
type instance AppRShape ((down :: Trace -> Lam -> Trace) up (App l r)) = AppR (down up (App l r)) r

relevantRight :: Traced Classical env -> Maybe (SameShape Classical env)
relevantRight env@(EmptyRoot a@(APP _ _)) = return $ Righty (AppRight env a)
relevantRight env@(AbsDown _ (LAM a@(APP _ _))) = return $ Righty (AppRight env a)
relevantRight env@(AppLeft _ (APP a@(APP _ _) _)) = return $ Righty (AppRight env a)
relevantRight env@(AppRight _ (APP _ a@(APP _ _))) = return $ Righty (AppRight env a)
relevantRight _ = Nothing

type family AbsDShape (env :: Trace) :: Trace
type instance AbsDShape (Root (Abs d)) = AbsD (Root (Abs d)) d
type instance AbsDShape ((down :: Trace -> Lam -> Trace) up (Abs d)) = AbsD (down up (Abs d)) d

relevantDown :: Traced Classical env -> Maybe (SameShape Classical env)
relevantDown env@(EmptyRoot l@(LAM _)) = return $ Downy (AbsDown env l)
relevantDown env@(AbsDown _ (LAM l@(LAM _))) = return $ Downy (AbsDown env l)
relevantDown env@(AppLeft _ (APP l@(LAM _) _)) = return $ Downy (AbsDown env l)
relevantDown env@(AppRight _ (APP _ l@(LAM _))) = return $ Downy (AbsDown env l)
relevantDown _ = Nothing

-- prove a Ref by looking at last *step* where we passed by
--
proveRef :: Classical (Ref more) -> Traced Classical env -> Maybe (Proven (Ref more) env)
proveRef HERE (AbsDown _ _) = return $ ProvenRefUp TrivialRef
proveRef HERE (AppLeft _ _) = return $ ProvenRefUp TrivialRef
proveRef HERE (AppRight _ _) = return $ ProvenRefUp TrivialRef
proveRef STOP _ = return $ TrivialRef
proveRef l@(LEFT more) env = do Lefty down@(AppLeft _ _) <- relevantLeft env
                                proof <- proveRef more down
                                return $ case proof of
                                         p@TrivialRef -> ProvenRefLeft p
                                         p@(ProvenRefLeft _) -> ProvenRefLeft p
                                         p@(ProvenRefRight _) -> ProvenRefLeft p
                                         p@(ProvenRefDown _) -> ProvenRefLeft p
proveRef l@(RIGHT more) env = do Righty down@(AppRight _ _) <- relevantRight env
                                 proof <- proveRef more down
                                 return $ case proof of
                                          p@TrivialRef -> ProvenRefRight p
                                          p@(ProvenRefLeft _) -> ProvenRefRight p
                                          p@(ProvenRefRight _) -> ProvenRefRight p
                                          p@(ProvenRefDown _) -> ProvenRefRight p

proveRef (DOWN more) env = do Downy down@(AbsDown _ _) <- relevantDown env
                              proof <- proveRef more down
                              return $ case proof of
                                       p@TrivialRef -> ProvenRefDown p
                                       p@(ProvenRefLeft _) -> ProvenRefDown p
                                       p@(ProvenRefRight _) -> ProvenRefDown p
                                       p@(ProvenRefDown _) -> ProvenRefDown p

proveRef (UP and) (AbsDown up _) = do proof <- proveRef and up
                                      return $ case proof of
                                               p@(ProvenRefUp _) -> ProvenRefUp p
                                               p@(ProvenRefDown _) -> ProvenRefUp p
proveRef (UP and) (AppLeft up _) = do proof <- proveRef and up
                                      return $ case proof of
                                               p@(ProvenRefUp _) -> ProvenRefUp p
                                               p@(ProvenRefLeft _) -> ProvenRefUp p
                                               p@(ProvenRefRight _) -> ProvenRefUp p
proveRef (UP and) (AppRight up _) = do proof <- proveRef and up
                                       return $ case proof of
                                                p@(ProvenRefUp _) -> ProvenRefUp p
                                                p@(ProvenRefLeft _) -> ProvenRefUp p
                                                p@(ProvenRefRight _) -> ProvenRefUp p

proveRef _ _ = Nothing

-- arrived under an Abs
--
proveUnderAbs :: Classical sh -> Traced Classical (AbsD env sh) -> Maybe (Proven (Abs sh) env)
proveUnderAbs h@HERE env = fmap ProvenAbs (proveRef h env)
proveUnderAbs u@(UP _) env = do proof <- proveRef u env
                                return $ case proof of
                                         p@(ProvenRefUp _) -> ProvenAbs p
proveUnderAbs a@(APP l r) env = do proof <- proveApp a env
                                   return $ case proof of
                                            p@(ProvenApp _ _) -> ProvenAbs p
proveUnderAbs v@(LAM a) env = do proof <- proveDown a (AbsDown env v)
                                 return $ case proof of
                                          p@(ProvenAbs _) -> ProvenAbs $ ProvenAbs p
                                          p@(ProvenApp _ _) -> ProvenAbs $ ProvenAbs p
                                          p@(ProvenRefUp _) -> ProvenAbs $ ProvenAbs p


-- Arrived at an App.
-- prove both directions
--
proveApp :: (Shape env ~ App l r) => Classical (App l r) -> Traced Classical env -> Maybe (Proven (App l r) env)
proveApp a@(APP l r) env = do proofL <- proveDown l (AppLeft env a)
                              proofR <- proveDown r (AppRight env a)
                              return $ case (proofL, proofR) of
                                       (p@(ProvenAbs _), q@(ProvenAbs _)) -> ProvenApp p q
                                       (p@(ProvenApp _ _), q@(ProvenAbs _)) -> ProvenApp p q
                                       (p@(ProvenRefUp _), q@(ProvenAbs _)) -> ProvenApp p q
                                       (p@(ProvenAbs _), q@(ProvenApp _ _)) -> ProvenApp p q
                                       (p@(ProvenApp _ _), q@(ProvenApp _ _)) -> ProvenApp p q
                                       (p@(ProvenRefUp _), q@(ProvenApp _ _)) -> ProvenApp p q
                                       (p@(ProvenAbs _), q@(ProvenRefUp _)) -> ProvenApp p q
                                       (p@(ProvenApp _ _), q@(ProvenRefUp _)) -> ProvenApp p q
                                       (p@(ProvenRefUp _), q@(ProvenRefUp _)) -> ProvenApp p q


-- We have just made a step (recorded in env) and arrived at some
-- unknown shape. Analyse first argument.
--
proveDown :: (Shape env ~ sh) => Classical sh -> Traced Classical env -> Maybe (Proven sh env)
proveDown h@HERE env = proveRef h env
proveDown u@(UP and) env = proveRef u env
proveDown v@(LAM down) env = proveUnderAbs down (AbsDown env v)
proveDown a@(APP _ _) env = proveApp a env

data Classical :: Lam -> * where
  LAM :: Classical sh -> Classical (Abs sh)
  APP :: Classical left -> Classical right -> Classical (App left right)
  HERE :: Classical (Ref '[Up])
  UP :: Classical (Ref more) -> Classical (Ref (Up ': more))
  LEFT :: Classical (Ref more) -> Classical (Ref (Le ': more))
  RIGHT :: Classical (Ref more) -> Classical (Ref (Ri ': more))
  DOWN :: Classical (Ref more) -> Classical (Ref (Down ': more))
  STOP :: Classical (Ref '[])

deriving instance Show (Classical sh)

instance Builder Classical where
  lam = LAM
  app = APP
  here = HERE
  up = UP
  checkClosure = flip proveDown


-- TESTS
-- ######

t1 = lam HERE
t1' = close (EmptyRoot t1) t1

t2 = app t1 t1
t2' = close (EmptyRoot t2) t2
t2'' = proveDown t2 (EmptyRoot t2)

t3 = app t1 (lam $ up $ up HERE)
-- t3' = close (EmptyRoot t3) t3
t3'' = proveDown t3 (EmptyRoot t3)

t4 = app t1 (lam $ up HERE)
t4' = close (EmptyRoot t4) t4
t4a' = close (AppRight (EmptyRoot t4) t4) t4
t4'' = proveDown t4 (EmptyRoot t4)

t5 = app t1 (lam $ up $ up $ LEFT $ STOP)
t5' = close (EmptyRoot t5) t5
t5'b = close (AppRight (EmptyRoot t5) t5) (lam $ up $ up $ LEFT $ STOP)
t5'' = proveDown t5 (EmptyRoot t5)

t6 = app t1 (lam $ up $ up $ RIGHT $ STOP)
t6' = close (EmptyRoot t6) t6
t6'b = close (AppRight (EmptyRoot t6) t6) (lam $ up $ up $ RIGHT $ STOP)
t6'' = proveDown t6 (EmptyRoot t6)


t7a = lam $ lam HERE
t7b = lam $ up $ up $ LEFT $ DOWN $ STOP
t7 = app t7a t7b
t7' = close (EmptyRoot t7) t7
t7'b = close (AppRight (EmptyRoot t7) t7) t7b
t7'' = proveDown t7 (EmptyRoot t7)

