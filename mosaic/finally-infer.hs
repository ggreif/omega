{-# LANGUAGE DataKinds, KindSignatures #-}
import GHC.TypeLits
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

-- stratified simply-typed first-order lambda calculus
-- in finally-tagless (typed) HOAS form

class LC (a :: Nat -> *) where
  (&) :: a l -> a l -> a l
  star :: a 2
  int :: a 1
  zero :: a 0
  inc :: a 0
  lam :: (a l -> a l) -> a l
  annotInt :: a 0 -> a 0

one, two, three :: LC a => a 0
one = inc & zero
two = twice inc & zero
three = inc & two
twice f = lam (\a -> f & (f & a))

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
  annotInt = id

newtype Str (l :: Nat) = Str String deriving Show
unStr (Str a) = a
instance LC Str where
  zero = Str "Z"
  inc = Str "S"
  lam f = Str $ "\a->" ++ unStr (f (Str "a"))
  Str f & Str a = Str $ "(" ++ f ++ " & " ++ a ++ ")"
  annotInt (Str a) = Str $ "(" ++ a ++ " :: Int)"

-- interpret these into a primitive type universe
data Univ (l :: Nat) = Int | Univ l `Arr` Univ l | Unkn (Ref l) deriving (Show, Eq)
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
  annotInt Int = Int
  annotInt (Unkn r) | f <- r `unifies` Int = f (Unkn r)

unifies (Ref r) (Unkn _) = error "UNIMPL!"


unifies (Ref r) a = case current of
                        Just a' | a' == a -> id
                        Nothing -> unsafePerformIO $ (writeIORef r (Just a) >> return id)
                        Just other -> error $ "cannot unify: " ++ show a ++ " and " ++ show other
  where current = unsafePerformIO $ readIORef r
        