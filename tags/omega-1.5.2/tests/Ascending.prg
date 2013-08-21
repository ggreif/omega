import "../tests/NatList.prg"

prop LE :: Nat ~> Nat ~> * where
  Klar :: LE Z x
  Schritt :: LE m n -> LE (S m) (S n)

-- proposition whether we can join a Nat with an already strictly monotone inventory
--
prop LEInv :: Inventory Nat ~> Nat ~> * where
  Egal :: LEInv []i n
  Laenger :: LE (S m) n -> LEInv inv m -> LEInv [inv; m]i n


-- value-level data types
--
data AscendingNats :: Inventory Nat ~> * where
  EmptyNats :: AscendingNats  []i
  MoreNats :: LEInv inv n => AscendingNats inv -> Nat' n -> AscendingNats [inv; n]i
 deriving LeftList(an)

-- merging of AscendingNats
--
mergeAscending :: AscendingNats linv -> AscendingNats rinv -> Maybe (AscendingNats {merge linv rinv})
mergeAscending []an r = Just r
mergeAscending (l@[lrest; ltop]an) []an = Just l
mergeAscending (linv@[lrest; ltop]an) (rinv@[rrest; rtop]an) = merge' ltop rtop linv rinv
  where merge' :: Nat' l -> Nat' r -> AscendingNats linv -> AscendingNats rinv
                         -> Maybe (AscendingNats {arrange l r linv rinv})
        merge' 0v (1+_)v (linv@[lrest; ltop]an) [rrest; rtop]an = do llr <- mergeAscending linv rrest
                                                                     lei <- tryLEInv llr rtop
                                                                     return [llr; rtop]an
        merge' (1+_)v 0v [lrest; ltop]an (rinv@[rrest; rtop]an) = do lrr <- mergeAscending lrest rinv
                                                                     lei <- tryLEInv lrr ltop
                                                                     return [lrr; ltop]an
        merge' (1+l)v (1+r)v linv rinv = merge' l r linv rinv
        merge' _ _ _ _ = Nothing

mergeAscending _ _ = Nothing

tryLE :: Nat' a -> Nat' b -> Maybe (LE a b)
tryLE 0v b = Just Klar
tryLE (1+a)v 0v = Nothing
tryLE (1+a)v (1+b)v = do { le <- tryLE a b; return (Schritt le) }

tryLEInv :: AscendingNats i -> Nat' b -> Maybe (LEInv i b)
tryLEInv []an b = Just Egal
tryLEInv [rest; a]an b = do le <- tryLE (S a) b
                            lei <- tryLEInv rest a
                            return (Laenger le lei)
