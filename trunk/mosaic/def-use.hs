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
  lam :: KnownPlace du => ((forall u . KnownPlace u => lc (Abs' du) u) -> lc d' (Abs' du)) -> lc du du
  (&) :: KnownPlace du => lc d' (Lunder' du) -> lc d'' (Runder' du) -> lc du du

-- singleton type isomorphic to (promoted) kind Place'
data Place :: Place' -> * where
  Root :: Place Root'
  Abs :: KnownPlace p => Place (Abs' p)
  Lunder :: KnownPlace p => Place (Lunder' p)
  Runder :: KnownPlace p => Place (Runder' p)

--deriving instance Show (Place p)
instance Show (Place p) where
  show Root = "Root"
  show p@Abs = "Abs("++show (par p)++")"
  show p@Lunder = "Lunder("++show (par p)++")"
  show p@Runder = "Runder("++show (par p)++")"

par :: KnownPlace par => Place (p par) -> Place par
par _ = thePlace

-- Def-Use markers

----------- def       use
data Lam :: Place' -> Place' -> * where
  Dummy :: (KnownPlace d, KnownPlace u) => Lam d u -- only for Show!
  L :: KnownPlace du => ((forall u . KnownPlace u => Lam (Abs' du) u) -> Lam d' (Abs' du)) -> Lam du du
  (:&) :: KnownPlace du => Lam d' (Lunder' du) -> Lam d'' (Runder' du) -> Lam du du

instance Show (Lam def use) where
  show lam@(L f) = "(\\" ++ show (f Dummy) ++ ")" ++ duStr lam
  show all@(f :& a) = "(" ++ show f ++ " & " ++ show a ++ ")" ++ duStr all
  show d@Dummy = duStr d

-- interpret LC semantics into Lam
instance LC Lam where lam = L; (&) = (:&)

duStr :: forall def use . (KnownPlace def, KnownPlace use) => Lam def use -> String
duStr l = "d" ++ place2str (def l) ++ "u" ++ place2str (use l)
  where place2str :: Place p -> String
        --place2str = show
        place2str = filter isUpper . show

def :: KnownPlace def => Lam def use -> Place def
def _ = thePlace
use :: KnownPlace use => Lam def use -> Place use
use _ = thePlace

test :: (KnownPlace u, LC lc) => lc u u
test = lam $ \a -> a & a        -- self-application
test' :: (KnownPlace u, LC lc) => lc u u
test' = lam $ \x->x             -- identity
test'' :: (KnownPlace u, LC lc) => lc u u
test'' = lam $ \x->lam $ \_->x  -- K combinator

tapp, tapp' :: (KnownPlace u, LC lc) => lc u u
tapp' = (lam $ \x->x) & (lam $ \a -> a & a)
tapp = test' & test
