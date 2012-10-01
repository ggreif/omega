import "../src/LangPrelude.prg" (maybeM)

data Thrist :: (l ~> l ~> *) ~> l ~> l ~> * where
  Nil :: Thrist k a a
  Cons :: k a b -> Thrist k b c -> Thrist k a c
 deriving List(t)

data Multiplicity :: *2 where
  Mono :: Multiplicity
  Poly :: Multiplicity

data Lev :: Multiplicity ~> *1 where
  ValueLevel :: Lev Mono
  LevelUp :: Lev m ~> Lev m
  PolyLevel :: Lev Poly -- level n .
 deriving syntax (lev) Nat(ValueLevel, LevelUp)

data HiddenLev :: *1 where
  HideLev :: Lev m ~> HiddenLev

data Level :: Lev n ~> * where
  ValueLevel :: Level ValueLevel
  LevelUp :: Level l -> Level (LevelUp l)
  PolyLevel :: Level PolyLevel
 deriving syntax (l) Nat(ValueLevel, LevelUp)

data Signature = Sig

data Iceberg :: * ~> * ~> * where
  Constructor :: Label t -> Level l -> Signature -> Iceberg () ()

data Icename :: Tag ~> Tag ~> * where -- entities with certain name
  NamedConstructor :: Label t -> Level l -> Signature -> Icename t t

--data Icelevel :: HiddenLev ~> HiddenLev ~> * where -- entities with certain level
--  LevelConstructor :: Label t -> Level l -> Signature -> Icelevel (HideLev l) (HideLev l)

data Icelevel' :: Lev n ~> Lev n ~> * where -- entities with certain level
  LevelConstructor' :: LevelSubsumes l' l => Label t -> Level l -> Signature -> Icelevel' l' l'


builtIn :: Thrist Iceberg () ()
builtIn = [ Constructor `Z 0l Sig, Constructor `S 0l Sig, Constructor natPrime 0l Sig
          , Constructor `Z 1l Sig, Constructor `S 1l Sig, Constructor `Nat 2l Sig
          , Constructor starN (LevelUp PolyLevel) Sig
          , Constructor constraintN (LevelUp PolyLevel) Sig]t
  where HideLabel natPrime = newLabel "Nat'"
        HideLabel starN = newLabel "*n"
        HideLabel constraintN = newLabel "#n"

projectName :: Label l -> Thrist Iceberg () () -> Thrist Icename l l
projectName _ []t = []t
projectName l [Constructor l' lev sig; rest]t = case sameLabel l l' of
                                                L Eq -> [NamedConstructor l' lev sig; projectName l rest]t
                                                _ -> projectName l rest



-- should be LevelFits
prop LevelSubsumes :: Lev n ~> Lev n' ~> * where
  BothValue :: LevelSubsumes ValueLevel ValueLevel
  BothPoly :: LevelSubsumes PolyLevel PolyLevel
  BothUp :: LevelSubsumes k k' -> LevelSubsumes (LevelUp k) (LevelUp k')
  UpValuePoly :: LevelSubsumes (LevelUp ValueLevel) PolyLevel
  --Commutes :: LevelSubsumes k k' => LevelSubsumes k' k -- NOT!


-- should be 'fits'
subsumes :: Level l -> Level l' -> Maybe (LevelSubsumes l l')
subsumes ValueLevel ValueLevel = Just BothValue
subsumes PolyLevel PolyLevel = Just BothPoly
subsumes (LevelUp l) (LevelUp l') = do ev <- subsumes l l'
                                       return $ BothUp ev
                                     where monad maybeM
subsumes (LevelUp ValueLevel) PolyLevel = Just UpValuePoly
subsumes _ _ = Nothing

projectLevel' :: Level l -> Thrist Iceberg () () -> Thrist Icelevel' l l
projectLevel' _ []t = []t
projectLevel' l [Constructor t l' sig; rest]t = case subsumes l l' of
                                               Just BothValue -> [LevelConstructor' t l' sig; projectLevel' l rest]t
                                               Just BothPoly -> [LevelConstructor' t l' sig; projectLevel' l rest]t
                                               Just (BothUp below) -> [LevelConstructor' t l' sig; projectLevel' l rest]t
                                               Just UpValuePoly -> [LevelConstructor' t l' sig; projectLevel' l rest]t
                                               _ -> projectLevel' l rest
