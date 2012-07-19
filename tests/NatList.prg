import "../src/LangPrelude.prg" (maybeM)
import "Inventory.prg"

data NatList :: Inventory Nat ~> * where
  Nope :: NatList []i
  Augment :: NatList i -> Nat' n -> NatList [i; n]i
 deriving LeftList(nl)


data LeftThrist :: forall (l :: *1) . (l ~> l ~> *)  ~> l ~> l ~> * where
  LNil :: LeftThrist k a a
  LCons :: LeftThrist k a b -> k b c -> LeftThrist k a c
 deriving LeftList(lt)

data Elem :: Inventory Nat ~> Inventory Nat ~> * where
  Single :: NatList nl -> Elem i {merge i nl}

monad maybeM

mergeNL :: NatList i -> NatList j -> Maybe (NatList {merge i j})
mergeNL []nl j = Just j
mergeNL (i@[as; a]nl) []nl = Just i
mergeNL [as; a]nl [bs; b]nl = arrNL as bs a b a b
mergeNL _ _ = Nothing


arrNL :: NatList i -> NatList j -> Nat' a' -> Nat' b' -> Nat' a -> Nat' b -> Maybe (NatList {arrange i j a' b' a b})
arrNL i j 0v (1+b')v a b = do { iaj <- mergeNL [i; a]nl j; return [iaj; b]nl }
arrNL i j (1+a')v 0v a b = do { ijb <- mergeNL i [j; b]nl; return [ijb; a]nl }
arrNL i j (1+a')v (1+b')v a b = arrNL i j a' b' a b
arrNL _ _ _ _ _ _ = Nothing

join :: NatList i -> LeftThrist Elem []i i -> NatList j -> Maybe (LeftThrist Elem []i {merge i j}, NatList {merge i j})
join i thr j = do { ij <- mergeNL i j
                  ; return ([thr; Single j]lt, ij) }

Just (t1, e1) = let start = [0v, 2v, 4v]nl in join start [Single start]lt [3v]nl
Just (t2, e2) = join e1 t1 [1v, 5v]nl


-- proposition for mergability
--
prop Disjoint :: Inventory Nat ~> Inventory Nat ~> * where
  WithEmpty :: Disjoint []i i
  WithLastAndRest :: Excluded n i -> Disjoint j i -> Disjoint [j; n]i i

-- exclusivity
--
prop Excluded :: Nat ~> Inventory Nat ~> * where
  NotInEmpty :: Excluded n []i
  NoZero :: Excluded 0t x -> Excluded 0t [x; (1+y)t]i
  NoHigher :: Excluded (1+n)t x -> Excluded (1+n)t [x; 0t]i
  ReduceToLower :: Excluded (1+n)t x -> Excluded n [y]i -> Excluded (1+n)t [x; (1+y)t]i

-- the total version of mergeNL
--
mergeNL' :: Disjoint i j => NatList i -> NatList j -> NatList {merge i j}
mergeNL' i j = let Just m = mergeNL i j in m

-- creating disjointness evidence
--
tryExcluded :: Nat' n -> NatList i -> Maybe (Excluded n i)
tryExcluded n []nl = Just NotInEmpty
tryExcluded 0v [x; (1+y)v]nl = do ev <- tryExcluded 0v x
                                  return (NoZero ev)
tryExcluded (1+n)v [x; 0v]nl = do ev <- tryExcluded (1+n)v x
                                  return (NoHigher ev)
tryExcluded (1+n)v [x; (1+y)v]nl = do ev1 <- tryExcluded (1+n)v x
                                      ev2 <- tryExcluded  n [y]nl
                                      return (ReduceToLower ev1 ev2)
