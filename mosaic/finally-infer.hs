{-# LANGUAGE DataKinds, KindSignatures, RankNTypes, StandaloneDeriving, GADTs, TypeOperators, FlexibleInstances, ViewPatterns #-}
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

--norm :: LC a => a l -> Norm l
--norm = id

unNorm :: LC a => Norm l -> a l
unNorm Zero = zero
unNorm Inc = inc
--unNorm (Lam f) = lam (\a -> unNorm $ f (norm a))
unNorm (f `App` a) = unNorm f & unNorm a
unNorm StarN = star
unNorm IntN = int
unNorm (name `InhN` ty) = name `inh` unNorm ty


-- interpret these into a primitive type universe
--           m   >= n      lev
data Univ :: Nat -> Nat -> Nat -> * where
  Int :: Univ m m l
  Arr :: Univ m n l -> Univ n o l -> Univ m o l
  IntTy :: Univ m m (1+l)
  Ty :: String -> Univ 0 0 (1+l) -> Univ m m l
  Inh :: String -> Univ 0 0 (1+l) -> Univ m m l
  Star :: Univ m m (2+l)
  Unkn :: Ref l -> Univ m m l

deriving instance Show (Univ m n l)
instance Eq (Univ 0 0 l) where
  Int == Int = True
  Star == Star = True
  IntTy == IntTy = True
  l `Arr` r == l' `Arr` r' = coerce00 l == coerce00 l' && coerce00 r == coerce00 r'
    where coerce00 :: Univ m n l -> Univ 0 0 l
          coerce00 = unsafeCoerce

data Ref l = Ref (IORef (Maybe (Univ 0 0 l)))
instance Show (Ref l) where
  show (Ref r) = "|" ++ show current ++ "|"
    where current = unsafePerformIO $ readIORef r
instance Eq (Ref l) where
  a == b = error "cannot compare Refs"

instance LC (Univ 0 0) where
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



-- possibly `fix` can help us avoiding two-hole contexts when unifying

class Defines a where
  (.:=) :: a -> a -> a  -- unify arguments
  ar :: a -> a -> a     -- form an arrow type
  intt :: a             -- the integer type
  split :: (a -> a -> a) -> (a -> a) -- check/infer variant of `ar`

class Defines a => Startable a where
  start :: (forall a . Defines a => a -> a) -> a -> a

data Uni where
  Whatnot :: (forall a . Defines a => a -> a) -> x -> Uni
  Intt :: Uni
  Ar :: Uni -> Uni -> Uni

instance Show Uni where
  show (Whatnot _ _) = "Whatnot"
  show Intt = "Intt"
  show (a `Ar` b) = "(" ++ show a ++ " `Ar` "  ++ show b ++ ")"

instance Defines Uni where
  Whatnot f _ .:= Whatnot g _ = fix' (g . f)
  -- Whatnot f a .:= r@(Whatnot _ _) = r .:= fix' f
  a .:= Whatnot _ _ = a
  Whatnot _ _ .:= b = b
  Intt .:= Intt = Intt
  (a `Ar` b) .:= (a' `Ar` b') = (a .:= a') `Ar` (b .:= b')
  a .:= b = error $ "cannot unify " ++ show (a,b)
  ar = Ar
  intt = Intt
  split f e = e .:= f (Whatnot id e) (Whatnot id e)
  --split f e = e .:= f (Whatnot (const $ error "tricky domain") e) (Whatnot (const $ error "tricky codomain") e)

instance Startable Uni where
  start = Whatnot

infixr 5 `ar`
infixr 4 .:=

fix' :: Startable a => (forall a . Defines a => a -> a) -> a
fix' f = let x = f (start f x) in x

-- Relevant:
-- http://www.cse.chalmers.se/~emax/documents/axelsson2013using.pdf
--
instance Defines Int where
  a .:= b = a `max` b
  dom `ar` cod = error "heh"


instance Startable Int where
  start f _ = 0

test, test2, test3, test4 :: Defines a => a -> a
test ex = ex .:= intt `ar` intt
test2 ex = (ex .:= intt `ar` intt) .:= intt
test3 ex = ex .:= ex
test4 = split (\ dom cod -> dom .:= cod `ar` cod)

{-
-- can we marry Defines and LC?
--                 check ---+    +--- infer
--                          v    v
newtype D a (l :: Nat) = D (a -> a)
dc a = D $ \x -> x .:= a
unD (D x) = x
fix'' :: Startable a => D a l -> a
fix'' (D f) = fix' f

instance Defines a => LC (D a) where
  zero = dc intt
  inc = dc $ intt `ar` intt
  --D f & D a =
  -- lam f = D $ \a -> let i = intt in a .:= i `ar` (unD (f (dc i)) undefined) -- TODO
  -- lam f = D $ split (\arg -> ) (id)
-}

-- Places in a lambda graph
--   how can this be injected into our HOAS?

data Place = Root | Lft Place | Rght Place | Def Place
class HOAS exp where
  app :: exp (Lft p) -> exp (Rght p) -> exp p
  lum :: (exp (Def p) -> exp p') -> exp p
  use :: exp (Def p) -> exp use

{- NEEDS moooore thought-}
tt1, tt2 :: HOAS exp => exp Root
tt1 = lum (\a -> use a `app` use a) `app` lum id
tt2 = lum (\a -> (lum id) `app` use a) `app` lum id




-- Zippers?

--data Zipper all part (l :: Nat) = Zipper part (part -> all)
data Zipper all (l :: Nat) = Zipper0 all | Zipper1 all (all -> all) | Zipper2 all (all -> all) all (all -> all)

allTogether (Zipper0 a) = a
allTogether (Zipper1 a a') = a' a
allTogether (Zipper2 a a' b b') = a' a & b' b

instance LC all => LC (Zipper (all l)) where
  -- Zipper1 f f' & Zipper1 a a' = Zipper2 (f' f) (& a' a) (a' a) (f' f &)
  (allTogether -> f) & (allTogether -> a) = Zipper2 f (& a) a (f &)
  -- Zipper f f' & Zipper a a' = Zipper (f' f) (& undefined)
  zero = Zipper0 zero
  inc = Zipper0 inc
