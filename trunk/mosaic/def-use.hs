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
  show Root = "rOot"
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
  -- NAT fragment
  Zero :: KnownPlace u => Lam ({-Named "zero"-}Lunder' (Runder' Root')) u
  Succ :: KnownPlace u => Lam ({-Named "succ"-}Runder' (Runder' Root')) u

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

-- flipped application
(|>) :: (LC lc, KnownPlace du) => lc d'' ('Runder' du) -> lc d' ('Lunder' du) -> lc du du
v |> f = f & v

-- fix in LC??  fix f = let x = f x in x


class NAT nat where
  zero :: KnownPlace u => nat ({-Named "zero"-}Lunder' (Runder' Root')) u
  succ :: KnownPlace u => nat ({-Named "succ"-}Runder' (Runder' Root')) u

instance NAT Lam where zero = Zero; succ = Succ

--- Type level?

class TY ty where
  int :: KnownPlace u => ty ({-Named "Int"-}Lunder' Root') u
  (~>) :: ty d'' (Runder' du) -> ty du du -> ty (Lunder' du) (Lunder' du)
  (.~.) :: ty d' u -> ty d u -> ty d u


  (~&) :: ty (Lunder' du) (Lunder' du) -> ty d'' (Runder' du) -> ty du du -- second projection of arrow
  split :: (ty d'' (Runder' du) -> ty du du -> ty du du) -> ty du du -- split arrow

--- interpret LC into TY: abstract interpretation of values into types
--    see dagstuhl paper Aaron Stump

data TyIterpr :: (Place' -> Place' -> *) -> Place' -> Place' -> * where
  --App :: KnownPlace du => TyIterpr d' (Lunder' du) -> TyIterpr d'' (Runder' du) -> TyIterpr du du
  Ty :: TY ty => ty d' u -> TyIterpr ty d u
  Arr :: TY ty => (ty (Abs' u) (Abs' u) -> ty (Abs' u) (Abs' u)) -> TyIterpr ty d u  -- TODO: should this be Ex? (existential tyvar intro?) fix that strips the (Ex v.)???

--unTy (Ty t) = t

--fix :: (ty d u -> ty d u) -> ty d u
--fix f = let x = f x in x

-- propagate uses to the type plane
above :: TY ty => (ty d' u -> TyIterpr ty d u) -> (ty d' u -> TyIterpr ty d u)
above = id

above2 :: TY ty => (ty d u -> TyIterpr ty d u) -> (ty d u -> TyIterpr ty d u)
above2 = id

{-
above2L :: TY ty => (ty (Lunder' d) (Lunder' u) -> TyIterpr ty d u)
                 -> (ty (Lunder' d) (Lunder' u) -> TyIterpr ty d u)
above2L = id
-}


instance TY ty => NAT (TyIterpr ty) where
  zero = above Ty int
  --succ = Ty (int~>int)

instance TY ty => LC (TyIterpr ty) where
  
  ---------lam f = Arr (\dom -> dom ~> unTy (f (Ty dom))) -- where dom = undefined
  --lam f = Ty . fix $ \dom -> dom ~> unTy (f (Ty dom))
  --lam f = above2L Ty . fix $ \dom -> dom ~> _ f dom
  lam f = above2 Ty (split $ \cod dom -> undefined) 
  Ty fty & Ty aty = let resty = (fty .~. (aty ~> resty)) ~& aty in above2 Ty resty

{- Place Diagram for lambda
+---------------------------------------------------+
           λ du:du                  ~> Ldu:Ldu      |
           |                       /  \             |
   Adu:u D -> C d':Adu            /    \            |
                                 /      \           |
                         Adu:u  D        C  d':Adu  |
-}

{- Place Diagram for application
+---------------------------------------------------+
           @ du:du                  B du:du         |
          / \                      / \              |
  d':Ldu F   A d'':Rdu            /   \             |
                                 /     \            |
                     d':Ldu F  ~>       A  d'':Rdu  |
                              /  \                  |
                             /    \                 |
                   d'':Rdu  A      B  du:du         |
-}