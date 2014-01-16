

data SK :: * ~> * where
  Var :: SK a
  KK :: SK (phy -> psy -> phy)
  SS :: SK ((phi -> psy -> nu) -> (phi -> psy) -> phi -> nu)
  App :: SK a -> SK b -> SK c
 deriving syntax (sk) LeftPair(App)

