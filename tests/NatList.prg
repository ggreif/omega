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

merge :: Inventory Nat ~> Inventory Nat ~> Inventory Nat
{merge []i i} = i
{merge [as; a]i []i} = [as; a]i
{merge [as; a]i [bs; b]i} = {arrange as bs a b a b}

mergeNL :: NatList i -> NatList j -> Maybe (NatList {merge i j})
mergeNL []nl j = Just j
mergeNL (i@[as; a]nl) []nl = Just i
mergeNL [as; a]nl [bs; b]nl = arrNL as bs a b a b
mergeNL _ _ = Nothing


arrange :: Inventory Nat ~> Inventory Nat ~> Nat ~> Nat ~> Nat ~> Nat ~> Inventory Nat
{arrange i j 0t (1+b')t a b} = [{merge [i; a]i j}; b]i
{arrange i j (1+a')t 0t a b} = [{merge i [j; b]i}; a]i
{arrange i j (1+a')t (1+b')t a b} = {arrange i j a' b' a b}

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
