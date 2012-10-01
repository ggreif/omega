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

data Icelevel :: Lev n ~> Lev n ~> * where -- entities with certain level
  LevelConstructor :: LevelFits l' l => Label t -> Level l -> Signature -> Icelevel l' l'


builtIns :: Thrist Iceberg () ()
builtIns = [ Constructor `Z 0l Sig, Constructor `S 0l Sig, Constructor natPrime 0l Sig
           , Constructor `Z 1l Sig, Constructor `S 1l Sig, Constructor `Nat 2l Sig
           , Constructor starN (LevelUp (LevelUp PolyLevel)) Sig
           , Constructor constraintN (LevelUp (LevelUp PolyLevel)) Sig
           , Constructor `MultValueAndUp PolyLevel Sig]t
  where HideLabel natPrime = newLabel "Nat'"
        HideLabel starN = newLabel "*n"
        HideLabel constraintN = newLabel "#n"

projectName :: Label l -> Thrist Iceberg () () -> Thrist Icename l l
projectName _ []t = []t
projectName l [Constructor l' lev sig; rest]t = case sameLabel l l' of
                                                L Eq -> [NamedConstructor l' lev sig; projectName l rest]t
                                                _ -> projectName l rest


-- inclusion relation on levels
--
prop LevelFits :: Lev n ~> Lev n' ~> * where
  BothValue :: LevelFits ValueLevel ValueLevel
  BothPoly :: LevelFits PolyLevel PolyLevel
  BothUp :: LevelFits k k' -> LevelFits (LevelUp k) (LevelUp k')
  ValuePoly :: LevelFits ValueLevel PolyLevel
  AbovePoly :: LevelFits (LevelUp k) PolyLevel

-- runtime compute level inclusion
--
fits :: Level l -> Level l' -> Maybe (LevelFits l l')
fits ValueLevel ValueLevel = Just BothValue
fits PolyLevel PolyLevel = Just BothPoly
fits (LevelUp l) (LevelUp l') = do ev <- fits l l'
                                   return $ BothUp ev
                                 where monad maybeM
fits ValueLevel PolyLevel = Just ValuePoly
fits (LevelUp l) PolyLevel = Just AbovePoly
fits _ _ = Nothing


projectLevel :: Level l -> Thrist Iceberg () () -> Thrist Icelevel l l
projectLevel _ []t = []t
projectLevel l [Constructor t l' sig; rest]t = case fits l l' of
                                               Just BothValue -> [LevelConstructor t l' sig; projectLevel l rest]t
                                               Just BothPoly -> [LevelConstructor t l' sig; projectLevel l rest]t
                                               Just (BothUp below) -> [LevelConstructor t l' sig; projectLevel l rest]t
                                               Just ValuePoly -> [LevelConstructor t l' sig; projectLevel l rest]t
                                               Just AbovePoly -> [LevelConstructor t l' sig; projectLevel l rest]t
                                               _ -> projectLevel l rest
