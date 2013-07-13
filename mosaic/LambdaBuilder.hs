{-# LANGUAGE KindSignatures, DataKinds, TypeOperators, StandaloneDeriving, GADTs,
             MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
             UndecidableInstances #-}

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
  checkClosure :: Traced env -> shape sh -> Proven env sh

class Closed (sh :: Lam) (env :: Trace)
instance Closed (Ref '[]) env
instance Closed (Ref more) up => Closed (Ref (Up ': more)) (VarD up sh)
instance Closed (Ref more) up => Closed (Ref (Up ': more)) (AbsD up sh)
instance Closed below (VarD env below) => Closed (Var below) env
instance Closed below (AbsD env below) => Closed (Abs below) env
instance (Closed left (AppL env left), Closed right (AppR env right)) => Closed (App left right) env


data Classical :: Lam -> * where
  LAM :: Classical sh -> Classical (Abs sh)
  APP :: Classical left -> Classical right -> Classical (App left right)
  VAR :: Classical sh -> Classical (Var sh)
  HERE :: Classical (Ref '[Up])

deriving instance Show (Classical sh)

instance Builder Classical where
  lam = LAM
  app = APP
  v = VAR
  here = HERE
  checkClosure (EmptyRoot _) HERE = NoWay
  checkClosure p@(VarDown up _) HERE = Goal p HERE
  checkClosure env a@(APP l r) = case (checkClosure (AppLeft env a) a, checkClosure (AppRight env a) a) of
                                 x -> undefined --(p1@(Goal _ _), p2@(Goal _ _)) -> ProvenApp (AppLeft env l, p1) (AppRight env r, p2)

-- We need a buildable tree of witnesses
-- later it will be parametrised in the constraint?
--
data Proven :: Trace -> Lam -> * where
  NoWay :: Proven env sh
  --LAM :: Classical sh -> Classical (Abs sh)
  ProvenApp :: -- (Closed left (AppL env left), Closed right (AppR env right)) =>
               Closed (App left right) env =>
               (Traced (AppL env left), Proven trL left) ->
               (Traced (AppR env right), Proven trR right) ->
               Proven env (App left right)
  --VAR :: Classical sh -> Classical (Var sh)
  Goal :: (Closed (Ref '[Up]) (VarD up sh), Builder l) => Traced (VarD up sh) -> l (Ref '[Up]) -> Proven (VarD up sh) (Ref '[Up])


-- TESTS
-- ######

t1 = v HERE
t1' = close (EmptyRoot t1) t1

t2 = app t1 t1
t2' = close (EmptyRoot t2) t2