{-# LANGUAGE KindSignatures, DataKinds, TypeOperators, StandaloneDeriving, GADTs,
             MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
             UndecidableInstances, TypeHoles, TypeFamilies #-}

-- See: https://code.google.com/p/omega/wiki/LambdaGraph
-- TODO: model "let(rec) a = sub in expr" with KILL1 @ sub (expr ... UP LEFT)
-- TODO: use Maybe instead of NoWay

data {-kind-} Lam = App Lam Lam | Abs Lam | Ref [Go]
data {-kind-} Go = Up | Le | Ri | Down

data {-kind-} Trace = Root Lam | AppL Trace Lam | AppR Trace Lam | AbsD Trace Lam

-- a zipper for lambda trees
--
data Traced :: (Lam -> *) -> Trace -> * where
  EmptyRoot :: Builder l => l sh -> Traced l (Root sh)
  AppLeft :: Builder l => Traced l tr -> l (App shl shr) -> Traced l (AppL tr shl)
  AppRight :: Builder l => Traced l tr -> l (App shl shr) -> Traced l (AppR tr shr)
  AbsDown :: Builder l => Traced l tr -> l (Abs sh) -> Traced l (AbsD tr sh)

deriving instance Show (Traced Classical tr)

class Builder (shape :: Lam -> *) where
  lam :: shape inner -> shape (Abs inner)
  app :: shape left -> shape right -> shape (App left right)
  here :: shape (Ref '[Up])
  up :: shape (Ref p) -> shape (Ref (Up ': p))
  close :: Closed sh env => Traced shape env -> shape sh -> shape sh
  close _ sh = sh
  checkClosure :: Traced shape env -> shape sh -> Proven sh env

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
  NoWay :: Proven sh env
  TrivialRef :: Proven (Ref '[]) env
  ProvenRefUp :: Closed (Ref more) env => Proven (Ref more) env -> Proven (Ref (Up ': more)) ((down :: Trace -> Lam -> Trace) env stuff)
  ProvenRefLeft :: CanGo more (Shape env) => Proven (Ref more) (AppL env stuff) -> Proven (Ref (Le ': more)) env
  ProvenRefRight :: CanGo more (Shape env) => Proven (Ref more) (AppR env stuff) -> Proven (Ref (Ri ': more)) env
  ProvenRefDown :: CanGo more (Shape env) => Proven (Ref more) (AbsD env stuff) -> Proven (Ref (Down ': more)) env
  ProvenApp :: (Closed l (AppL env l), Closed r (AppR env r)) =>
               Proven l (AppL env l) -> Proven r (AppR env r) ->
               Proven (App l r) env
  ProvenAbs :: Closed below (AbsD env below) =>
               Proven below (AbsD env below) -> Proven (Abs below) env

deriving instance Show (Proven sh env)

getShape :: Traced Classical env -> Classical (Shape env)
getShape (EmptyRoot a@(APP _ _)) = a
getShape (EmptyRoot a@(LAM _)) = a
getShape (AppLeft _ (APP l _)) = l
getShape (AppRight _ (APP _ r)) = r
getShape (AbsDown _ (LAM d)) = d


type family AppShape (env :: Trace) :: Trace
type instance AppShape (Root (App l r)) = (AppL (Root (App l r)) l)
type instance AppShape (AppL up sh) = (AppL up sh)
--type instance AppShape (AppR up sh) = Shape up

getAppShape :: Traced Classical env -> Traced Classical (AppShape env)
getAppShape env@(EmptyRoot a@(APP _ _)) = (AppLeft env a)
getAppShape env@(AppLeft up _) = env
--getAppShape (AppRight up _) = up


-- prove a Ref by looking at last *step* where we passed by
--
proveRef :: Classical (Ref more) -> Traced Classical env -> Proven (Ref more) env
proveRef HERE (AbsDown _ _) = ProvenRefUp TrivialRef
proveRef HERE (AppLeft _ _) = ProvenRefUp TrivialRef
proveRef HERE (AppRight _ _) = ProvenRefUp TrivialRef
proveRef STOP _ = TrivialRef
proveRef (LEFT more@(RIGHT STOP)) env@(EmptyRoot a@(APP _ _)) = case proveRef more (AppLeft env a) of
                                                 NoWay -> NoWay
                                                 p@TrivialRef -> ProvenRefLeft p
                                                 p@(ProvenRefLeft _) -> ProvenRefLeft p
                                                 p@(ProvenRefRight _) -> ProvenRefLeft p
--                                                 p@(ProvenRefDown _) -> ProvenRefLeft p
{-proveRef (RIGHT more) env | a@(APP _ _) <- getAppShape env = case proveRef more (AppRight env a) of
                                                 NoWay -> NoWay
                                                 p@TrivialRef -> ProvenRefRight p
                                                 p@(ProvenRefLeft _) -> ProvenRefRight p
                                                 p@(ProvenRefRight _) -> ProvenRefRight p
                                                 p@(ProvenRefDown _) -> ProvenRefRight p
proveRef (DOWN more) env | a@(LAM _) <- getShape env = case proveRef more (AbsDown env a) of
                                                 NoWay -> NoWay
                                                 p@TrivialRef -> ProvenRefDown p
                                                 p@(ProvenRefLeft _) -> ProvenRefDown p
                                                 p@(ProvenRefRight _) -> ProvenRefDown p
                                                 p@(ProvenRefDown _) -> ProvenRefDown p
-}
proveRef (UP and) (AbsDown up _) = case (proveRef and up) of
                                   NoWay -> NoWay
                                   p@(ProvenRefUp _) -> ProvenRefUp p
proveRef (UP and) (AppLeft up _) = case (proveRef and up) of
                                   NoWay -> NoWay
                                   p@(ProvenRefUp _) -> ProvenRefUp p
proveRef (UP and) (AppRight up _) = case (proveRef and up) of
                                    NoWay -> NoWay
                                    p@(ProvenRefUp _) -> ProvenRefUp p
                                    --p@(ProvenRefLeft _) -> p
                                    p -> error $ show p

proveRef _ _ = NoWay

-- arrived under an Abs
--
proveUnderAbs :: Classical sh -> Traced Classical (AbsD env sh) -> Proven (Abs sh) env
proveUnderAbs h@HERE env = ProvenAbs $ proveRef h env
proveUnderAbs u@(UP _) env = case proveRef u env of
                                NoWay -> NoWay
                                p@(ProvenRefUp _) -> ProvenAbs p
proveUnderAbs a@(APP l r) env = case proveApp a env of
                                NoWay -> NoWay
                                p@(ProvenApp _ _) -> ProvenAbs p
proveUnderAbs v@(LAM a) env = case proveDown a (AbsDown env v) of
                              NoWay -> NoWay
                              p@(ProvenAbs _) -> ProvenAbs $ ProvenAbs p
                              p@(ProvenApp _ _) -> ProvenAbs $ ProvenAbs p
                              p@(ProvenRefUp _) -> ProvenAbs $ ProvenAbs p
                              --p -> error $ show p


-- Arrived at an App.
-- prove both directions
--
proveApp :: Classical (App l r) -> Traced Classical env -> Proven (App l r) env
proveApp a@(APP l r) env = case (proveDown l (AppLeft env a), proveDown r (AppRight env a)) of
                           (NoWay, _) -> NoWay
                           (_, NoWay) -> NoWay
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
proveDown :: Classical sh -> Traced Classical env -> Proven sh env
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

