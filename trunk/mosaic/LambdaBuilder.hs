{-# LANGUAGE KindSignatures, DataKinds, TypeOperators, StandaloneDeriving, GADTs,
             MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
             UndecidableInstances, TypeHoles #-}

-- See: https://code.google.com/p/omega/wiki/LambdaGraph

data {-kind-} Lam = Var Lam | App Lam Lam | Abs Lam | Ref [Go]
data {-kind-} Go = Up | Le | Ri | Down

data {-kind-} Trace = Root Lam | VarD Trace Lam | AppL Trace Lam | AppR Trace Lam | AbsD Trace Lam

-- a zipper for lambda trees
--
data Traced :: Trace -> * where
  EmptyRoot :: Builder l => l sh -> Traced (Root sh)
  VarDown :: Builder l => Traced tr -> l (Var sh) -> Traced (VarD tr sh)
  AppLeft :: Builder l => Traced tr -> l (App shl shr) -> Traced (AppL tr shl)
  AppRight :: Builder l => Traced tr -> l (App shl shr) -> Traced (AppR tr shr)
  AbsDown :: Builder l => Traced tr -> l (Abs sh) -> Traced (AbsD tr sh)

--deriving instance Show (Traced tr)

class Builder (shape :: Lam -> *) where
  v :: shape inner -> shape (Var inner)
  lam :: shape inner -> shape (Abs inner)
  app :: shape left -> shape right -> shape (App left right)
  here :: shape (Ref '[Up])
  up :: shape (Ref p) -> shape (Ref (Up ': p))
  close :: Closed sh env => Traced env -> shape sh -> shape sh
  checkClosure :: Traced env -> shape sh -> Proven sh env

class Closed (sh :: Lam) (env :: Trace)
instance Closed (Ref '[]) env
instance Closed (Ref more) up => Closed (Ref (Up ': more)) ((down :: Trace -> Lam -> Trace) up sh)
instance Closed below (VarD env below) => Closed (Var below) env
instance Closed below (AbsD env below) => Closed (Abs below) env
--instance Closed below (AppL env below) => Closed (App below) env
--instance Closed below (AppR env below) => Closed (App below) env
instance (Closed left (AppL env left), Closed right (AppR env right)) => Closed (App left right) env

data Proven :: Lam -> Trace -> * where
  NoWay :: Proven sh env
  TrivialRef :: Proven (Ref '[]) env
  ProvenRefUp :: Closed (Ref more) env => Proven (Ref more) env -> Proven (Ref (Up ': more)) ((down :: Trace -> Lam -> Trace) env stuff)
  ProvenApp :: (Closed l (AppL env l), Closed r (AppR env r)) =>
               Proven l (AppL env l) -> Proven r (AppR env r) ->
               Proven (App l r) env
  ProvenVar :: Closed below (VarD env below) =>
               Proven below (VarD env below) -> Proven (Var below) env
  ProvenAbs :: Closed below (AbsD env below) =>
               Proven below (AbsD env below) -> Proven (Abs below) env

--prove :: Classical sh -> 

proveRef :: Classical (Ref more) -> Traced env -> Proven (Ref more) env
proveRef HERE (VarDown _ _) = ProvenRefUp TrivialRef
proveRef HERE (AbsDown _ _) = ProvenRefUp TrivialRef
proveRef HERE (AppLeft _ _) = ProvenRefUp TrivialRef
proveRef HERE (AppRight _ _) = ProvenRefUp TrivialRef
proveRef (UP and) (VarDown up _) = case (proveRef and up) of
                                   NoWay -> NoWay
                                   p@(ProvenRefUp _) -> ProvenRefUp p
proveRef (UP and) (AbsDown up _) = case (proveRef and up) of
                                   NoWay -> NoWay
                                   p@(ProvenRefUp _) -> ProvenRefUp p
proveRef (UP and) (AppLeft up _) = case (proveRef and up) of
                                   NoWay -> NoWay
                                   p@(ProvenRefUp _) -> ProvenRefUp p
proveRef (UP and) (AppRight up _) = case (proveRef and up) of
                                    NoWay -> NoWay
                                    p@(ProvenRefUp _) -> ProvenRefUp p
-- TODO: Le, Ri, Down


proveVar :: Classical (Var sh) -> Traced env -> Proven (Var sh) env
proveVar v@(VAR h@HERE) env = ProvenVar $ proveRef h (VarDown env v)
proveVar v@(VAR u@(UP _)) env = case proveRef u (VarDown env v) of
                                NoWay -> NoWay
                                p@(ProvenRefUp _) -> ProvenVar p
proveVar (VAR a@(APP _ _)) env = case proveApp a (AppLeft env a) of -- proveDown!!!
                                 NoWay -> NoWay
                                 p@(ProvenApp _ _) -> undefined -- ProvenVar p
proveVar v@(VAR a) env = case proveDown a (VarDown env v) of
                         NoWay -> NoWay
                         p@(ProvenAbs _) -> ProvenVar p
                         p@(ProvenVar _) -> ProvenVar p

proveApp :: Classical (App l r) -> Traced env -> Proven (App l r) env
proveApp app@(APP h@HERE h2@HERE) env@(AppLeft _ _) = case (proveRef h env) of
                                                      p@(ProvenRefUp _) -> ProvenApp (ProvenRefUp TrivialRef) undefined

proveAbs :: Classical (Abs sh) -> Traced env -> Proven (Abs sh) env
proveAbs a@(LAM h@HERE) env = ProvenAbs $ proveRef h (AbsDown env a)
-- TODO: all cases just like proveVar!


proveDown :: Classical sh -> Traced env -> Proven sh env
proveDown v@(VAR _) env@(VarDown _ _) = proveVar v env
proveDown a@(LAM _) env@(AbsDown _ _) = proveAbs a env
proveDown a@(APP l _) env@(AppLeft _ _) = proveApp a env
proveDown a@(APP _ r) env@(AppRight _ _) = proveApp a env

data Classical :: Lam -> * where
  LAM :: Classical sh -> Classical (Abs sh)
  APP :: Classical left -> Classical right -> Classical (App left right)
  VAR :: Classical sh -> Classical (Var sh)
  HERE :: Classical (Ref '[Up])
  UP :: Classical (Ref more) -> Classical (Ref (Up ': more))

deriving instance Show (Classical sh)

instance Builder Classical where
  lam = LAM
  app = APP
  v = VAR
  here = HERE
  up = UP


-- TESTS
-- ######

t1 = v HERE
t1' = close (EmptyRoot t1) t1

t2 = app t1 t1
t2' = close (EmptyRoot t2) t2

