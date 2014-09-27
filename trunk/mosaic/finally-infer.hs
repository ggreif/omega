{-# LANGUAGE DataKinds, KindSignatures, StandaloneDeriving, GADTs, TypeOperators, FlexibleInstances #-}
import GHC.TypeLits
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)
import Unsafe.Coerce (unsafeCoerce)

-- stratified simply-typed first-order lambda calculus
-- in finally-tagless (typed) HOAS form

class LC (a :: Nat -> *) where
  (&) :: a l -> a l -> a l
  star :: a (2+l)
  int :: a (1+l)
  inh :: String -> a (1+l) -> a l
  zero :: a l
  inc :: a l
  lam :: (a l -> a l) -> a l
  as :: a l -> a (1+l) -> a l
  lift :: a l -> a (1+l)

infixr `inh`

one, two, three :: LC a => a 0
one = inc & zero
two = twice inc & zero
three = inc & two
twice f = lam (\a -> f & (f & a))
twice' :: LC a => a 0
twice' = lam (\f -> twice f)

-- interpret these into Nat
data N (l :: Nat) = Z | S (N l) | F (N l -> N l)

instance Show (N l) where
  show (F _) = "<func>"
  show Z = "Z"
  show (S n) = 'S' : show n

instance LC N where
  zero = Z
  inc = F S
  F f & Z = f Z
  F f & a@(S _) = f a
  lam = F
  as a _ = a

newtype Str (l :: Nat) = Str String deriving Show
unStr (Str a) = a
instance LC Str where
  zero = Str "Z"
  inc = Str "S"
  lam f = Str $ "\a->" ++ unStr (f (Str "a"))
  Str f & Str a = Str $ "(" ++ f ++ " & " ++ a ++ ")"
  as (Str a) (Str t) = Str $ "(" ++ a ++ " :: " ++ show t ++ ")"
  inh name (Str parent) = Str $ name ++ " `inh` " ++ parent
  int = Str "Int"
  star = Str "*"

data Norm :: Nat -> * where
  Zero :: Norm l
  Inc :: Norm l
  Lam :: (Norm l -> Norm l) -> Norm l
  App :: Norm l -> Norm l -> Norm l
  StarN :: Norm (2+l)
  IntN :: Norm (1+l)
  InhN :: String -> Norm (1+l) -> Norm l
  -- Lift :: Norm l -> Norm (1+l) -- not needed, we use unsafeCoerce

deriving instance Show (Norm l)
instance Show (Norm l -> Norm l) where
  show _ = "<fn>"

instance LC Norm where
  zero = Zero
  inc = Inc
  lam = Lam
  Lam f & a = f a
  l & a = l `App` a
  v `as` _ = v
  star = StarN
  int = IntN
  inh = InhN
  lift = unsafeCoerce

unNorm :: LC a => Norm l -> a l
unNorm Zero = zero
unNorm Inc = inc
--unNorm (Lam f) = lam (\a -> unNorm $ f a)
unNorm (f `App` a) = unNorm f & unNorm a
unNorm StarN = star
unNorm IntN = int
unNorm (name `InhN` ty) = name `inh` unNorm ty


-- interpret these into a primitive type universe
data Univ (l :: Nat) where
  Int :: Univ l
  Arr :: Univ l -> Univ l -> Univ l
  IntTy :: Univ (1+l)
  Ty :: String -> Univ (1+l) -> Univ l
  Inh :: String -> Univ (1+l) -> Univ l
  Star :: Univ (2+l)
  Unkn :: Ref l -> Univ l

deriving instance Show (Univ l)
deriving instance Eq (Univ l)

data Ref l = Ref (IORef (Maybe (Univ l)))
instance Show (Ref l) where
  show (Ref r) = "|" ++ show current ++ "|"
    where current = unsafePerformIO $ readIORef r
instance Eq (Ref l) where
  a == b = error "cannot compare Refs"

instance LC Univ where
  --int = Int
  zero = Int
  inc = Int `Arr` Int
  (Int `Arr` c) & Int = c
  (Int `Arr` c) & Unkn r | f <- r `unifies` Int = f c
  (Unkn r `Arr` c) & a | f <- r `unifies` a = f c
  f & a = error $ '(' : show f ++ ") & (" ++ show a ++ ")"
  lam f = let u = Unkn (Ref (unsafePerformIO $ newIORef Nothing)) in f u `seq` (u `Arr` f u)
  as Int IntTy = Int
  as IntTy Star = IntTy
  as (Unkn r) IntTy | f <- r `unifies` Int = f (Unkn r)
  --as (Unkn r) t@(name `Inh` _) | f <- r `unifies` t = f (Unkn r)
  int = IntTy
  inh = Inh
  star = Star

unifies (Ref r) (Unkn _) = error "UNIMPL!"


unifies (Ref r) a = case current of
                        Just a' | a' == a -> id
                        Nothing -> unsafePerformIO $ (writeIORef r (Just a) >> return id)
                        Just other -> error $ "cannot unify: " ++ show a ++ " and " ++ show other
  where current = unsafePerformIO $ readIORef r
        