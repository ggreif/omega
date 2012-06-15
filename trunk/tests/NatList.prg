import "../src/LangPrelude.prg" (maybeM)

kind Inventory = Empty | More Inventory Nat deriving LeftList(i)

data NatList :: Inventory ~> * where
  Nope :: NatList []i
  Augment :: NatList i -> Nat' n -> NatList [i; n]i
 deriving LeftList(nl)


data LeftThrist :: forall (l :: *1) . (l ~> l ~> *)  ~> l ~> l ~> * where
  LNil :: LeftThrist k a a
  LCons :: LeftThrist k a b -> k b c -> LeftThrist k a c
 deriving LeftList(lt)

data Elem :: Inventory ~> Inventory ~> * where
  Single :: NatList nl -> Elem i {merge i nl}

monad maybeM

merge :: Inventory ~> Inventory ~> Inventory
{merge []i i} = i
{merge [as; a]i []i} = [as; a]i
{merge [as; a]i [bs; b]i} = {arrange {merge as bs} a b a b}

mergeNL :: NatList i -> NatList j -> Maybe (NatList {merge i j})
mergeNL []nl j = Just j
mergeNL (i@[as; a]nl) []nl = Just i
mergeNL [as; a]nl [bs; b]nl = do { abs <- mergeNL as bs
                                 ; arrNL abs a b a b }
mergeNL _ _ = Nothing


arrange :: Inventory ~> Nat ~> Nat ~> Nat ~> Nat ~> Inventory
{arrange i 0t (S b') a b} = [i; a, b]i
{arrange i (S a') 0t a b} = [i; b, a]i
{arrange i (S a') (S b') a b} = {arrange i a' b' a b}

arrNL :: NatList i -> Nat' a' -> Nat' b' -> Nat' a -> Nat' b -> Maybe (NatList {arrange i a' b' a b})
arrNL i 0v (1+b')v a b = Just [i; a, b]nl
arrNL i (1+a')v 0v a b = Just [i; b, a]nl
arrNL i (1+a')v (1+b')v a b = arrNL i a' b' a b
arrNL _ _ _ _ _ = Nothing

join :: NatList i -> LeftThrist Elem []i i -> NatList j -> Maybe (LeftThrist Elem []i {merge i j}, NatList {merge i j})
join i thr j = do { ij <- mergeNL i j
                  ; return ([thr; Single j]lt, ij) }

Just (t1, e1) = join [0v, 2v, 4v]nl [Single [0v, 2v, 4v]nl]lt [3v]nl
Just (t2, e2) = join e1 t1 [8v]nl
