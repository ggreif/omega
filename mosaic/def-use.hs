{-# LANGUAGE DataKinds, KindSignatures, RankNTypes, StandaloneDeriving, GADTs, TypeOperators
           , FlexibleInstances, ViewPatterns, MultiParamTypeClasses #-}


import Data.Char (isUpper)

--                    var intro              v--- app ---v
data Place' = Root' | Abs' Place' | Lunder' Place' | Runder' Place'

class KnownPlace (p :: Place') where
  thePlace :: Place p

-- value inference for a place type
instance KnownPlace Root' where thePlace = Root
instance KnownPlace p => KnownPlace (Abs' p) where thePlace = Abs
instance KnownPlace p => KnownPlace (Lunder' p) where thePlace = Lunder
instance KnownPlace p => KnownPlace (Runder' p) where thePlace = Runder

-- define semantics
class LC (lc :: Place' -> Place' -> *) where
  lam :: (KnownPlace def, KnownPlace use) => ((forall u . KnownPlace u => lc (Abs' def) u) -> lc (Abs' def) use) -> lc def use
  (&) :: (KnownPlace d, KnownPlace u) => lc d' (Lunder' d) -> lc d'' (Runder' d) -> lc d u

-- singleton type isomorphic to (promoted) kind Place'
data Place :: Place' -> * where
  Root :: Place Root'
  Abs :: KnownPlace p => Place (Abs' p)
  Lunder :: KnownPlace p => Place (Lunder' p)
  Runder :: KnownPlace p => Place (Runder' p)

deriving instance Show (Place p)


-- Def-Use markers

----------- def       use
data Lam :: Place' -> Place' -> * where
  Dummy :: (KnownPlace d, KnownPlace u) => Lam d u -- only for Show!
  L :: (KnownPlace d, KnownPlace u) => ((forall u . KnownPlace u => Lam (Abs' d) u) -> Lam (Abs' d) u) -> Lam d u
  (:&) :: (KnownPlace d, KnownPlace u) => Lam d' (Lunder' d) -> Lam d'' (Runder' d) -> Lam d u

instance Show (Lam def use) where
  show lam@(L f) = "(\\" ++ show (f Dummy) ++ ")" ++ duStr lam
  show all@(f :& a) = "(" ++ show f ++ " & " ++ show a ++ ")" ++ duStr all
  show d@Dummy = duStr d

-- interpret LC semantics into Lam
instance LC Lam where lam = L; (&) = (:&)

duStr :: forall def use . (KnownPlace def, KnownPlace use) => Lam def use -> String
duStr l = "d" ++ place2str (def l) ++ "u" ++ place2str (use l)
  where place2str :: Place p -> String
        place2str = filter isUpper . show

def :: KnownPlace def => Lam def use -> Place def
def _ = thePlace
use :: KnownPlace use => Lam def use -> Place use
use _ = thePlace

test :: (lc ~ Lam, LC lc) => lc Root' (Lunder' Root')
test = lam $ \a -> a & a
test' :: (lc ~ Lam, LC lc) => lc Root' Root'
test' = lam $ \x->x
test'' :: (lc ~ Lam, LC lc) => lc Root' Root'
test'' = lam $ \x->lam $ \x->x
