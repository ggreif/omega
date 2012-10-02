-- implement the idea described in
-- https://code.google.com/p/omega/wiki/IcebergTypes
--

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

data Level :: Lev n ~> * where
  ValueLevel :: Level ValueLevel
  LevelUp :: Level l -> Level (LevelUp l)
  PolyLevel :: Level PolyLevel
 deriving syntax (l) Nat(ValueLevel, LevelUp)

data Signature :: * where
  Sig :: Signature -- some signature (for now)
  SigCtor :: Label t -> Signature
  SigFun :: Label t -> Signature
  SigVar :: Label t -> Signature
  SigApp :: Signature -> Signature -> Signature

data Iceberg :: * ~> * ~> * where
  Constructor :: Label t -> Level l -> Signature -> Iceberg () ()

data Icename :: Tag ~> Tag ~> * where -- entities with certain name
  NamedConstructor :: Label t -> Level l -> Signature -> Icename t t

data Icelevel :: Lev n ~> Lev n ~> * where -- entities with certain level
  LevelConstructor :: LevelFits l' l => Label t -> Level l -> Signature -> Icelevel l' l'

data TagLev :: Multiplicity ~> *1 where
  TL :: Tag ~> Lev m ~> TagLev m

data Icenamelevel :: TagLev n ~> TagLev n ~> * where -- entities with certain level and name
  NamedLevelConstructor :: LevelFits l' l => Label t -> Level l -> Signature -> Icenamelevel (TL t l') (TL t l')


builtIns :: Thrist Iceberg () ()
builtIns = [ Constructor `Z 0l $ SigApp (SigCtor natPrime) (SigCtor `Z)
           , Constructor `S 0l $ SigApp (SigApp (SigCtor varrow) (SigApp (SigCtor natPrime) $ SigVar `a)) (SigApp (SigCtor natPrime) $ (SigApp (SigCtor `S) $ SigVar `a))
           , Constructor natPrime 0l $ SigApp (SigApp (SigCtor karrow) (SigCtor `Nat)) (SigCtor starN)
           , Constructor `Z 1l $ SigCtor `Nat
           , Constructor `S 1l $ SigApp (SigApp (SigCtor karrow) (SigCtor `Nat)) (SigCtor `Nat)
           , Constructor `Nat 2l Sig
           , Constructor starN (LevelUp (LevelUp PolyLevel)) Sig
           , Constructor constraintN (LevelUp (LevelUp PolyLevel)) Sig
           , Constructor varrow 1l Sig
           , Constructor `MultValueAndUp PolyLevel Sig]t
  where HideLabel natPrime = newLabel "Nat'"
        HideLabel starN = newLabel "*n"
        HideLabel constraintN = newLabel "#n"
        HideLabel varrow = newLabel "->"
        HideLabel karrow = newLabel "~>"

projectName :: Label l -> Thrist Iceberg () () -> Thrist Icename l l
projectName _ []t = []t
projectName l [Constructor l' lev sig; rest]t = case l `sameLabel` l' of
                                                L Eq -> [NamedConstructor l' lev sig; projectName l rest]t
                                                _ -> projectName l rest


projectName' :: Label t -> Thrist Icelevel l l -> Thrist Icenamelevel (TL t l) (TL t l)
projectName' _ []t = []t
projectName' t [LevelConstructor t' lev sig; rest]t = case t `sameLabel` t' of
                                                      L Eq -> [NamedLevelConstructor t' lev sig; projectName' t rest]t
                                                      _ -> projectName' t rest


-- inclusion relation on levels
--
prop LevelFits :: Lev n ~> Lev n' ~> * where
  BothValue :: LevelFits ValueLevel ValueLevel
  InPoly :: LevelFits k PolyLevel
  BothUp :: LevelFits k k' -> LevelFits (LevelUp k) (LevelUp k')

-- runtime compute level inclusion
--
fits :: Level l -> Level l' -> Maybe (LevelFits l l')
fits ValueLevel ValueLevel = Just BothValue
fits (LevelUp l) (LevelUp l') = do ev <- fits l l'
                                   return $ BothUp ev
                                 where monad maybeM
fits _ PolyLevel = Just InPoly
fits _ _ = Nothing

multiplicity :: Multiplicity ~> Multiplicity ~> Multiplicity
{multiplicity Mono b} = Mono
{multiplicity Poly b} = b

unilev :: Lev a ~> Lev b ~> Lev {multiplicity a b}
{unilev ValueLevel ValueLevel} = ValueLevel
{unilev ValueLevel PolyLevel} = ValueLevel
{unilev (LevelUp a) (LevelUp b)} = LevelUp {unilev a b}
{unilev (LevelUp a) PolyLevel} = LevelUp {unilev a PolyLevel}
{unilev PolyLevel ValueLevel} = ValueLevel
{unilev PolyLevel (LevelUp b)} = LevelUp {unilev PolyLevel b}
{unilev PolyLevel PolyLevel} = PolyLevel

-- prove commutativity
--
unifyCommutes :: Level k -> Level l -> Equal {unilev k l} {unilev l k}
unifyCommutes ValueLevel ValueLevel = Eq
unifyCommutes ValueLevel PolyLevel = Eq
unifyCommutes (LevelUp a) (LevelUp b) = Eq where theorem hyp = unifyCommutes a b
unifyCommutes (LevelUp a) PolyLevel = Eq where theorem hyp = unifyCommutes a PolyLevel
unifyCommutes PolyLevel ValueLevel = Eq
unifyCommutes PolyLevel (LevelUp b) = Eq where theorem hyp = unifyCommutes PolyLevel b
unifyCommutes PolyLevel PolyLevel = Eq

unifyLevels :: Level k -> Level l -> Maybe (Level {unilev k l})
unifyLevels ValueLevel (LevelUp b) = Nothing
unifyLevels ValueLevel ValueLevel = Just ValueLevel
unifyLevels ValueLevel PolyLevel = Just ValueLevel
unifyLevels (LevelUp a) (LevelUp b) = do yes <- unifyLevels a b
                                         return $ LevelUp yes
                                       where monad maybeM
unifyLevels (LevelUp a) ValueLevel = Nothing
unifyLevels (LevelUp a) PolyLevel = do yes <- unifyLevels a PolyLevel
                                       return $ LevelUp yes
                                     where monad maybeM
unifyLevels PolyLevel ValueLevel = unifyLevels ValueLevel PolyLevel
unifyLevels PolyLevel (LevelUp b) = unifyLevels (LevelUp b) PolyLevel
  where theorem comm = unifyCommutes PolyLevel b
unifyLevels PolyLevel PolyLevel = Just PolyLevel


projectLevel :: Level l -> Thrist Iceberg () () -> Thrist Icelevel l l
projectLevel _ []t = []t
projectLevel l [Constructor t l' sig; rest]t = case l `fits` l' of
                                               Just BothValue -> [LevelConstructor t l' sig; projectLevel l rest]t
                                               Just InPoly -> [LevelConstructor t l' sig; projectLevel l rest]t
                                               Just (BothUp below) -> [LevelConstructor t l' sig; projectLevel l rest]t
                                               _ -> projectLevel l rest


projectLevel' :: Level l -> Thrist Icename t t -> Thrist Icenamelevel (TL t l) (TL t l)
projectLevel' _ []t = []t
projectLevel' l [NamedConstructor t l' sig; rest]t = case l `fits` l' of
                                                     Just BothValue -> [NamedLevelConstructor t l' sig; projectLevel' l rest]t
                                                     Just InPoly -> [NamedLevelConstructor t l' sig; projectLevel' l rest]t
                                                     Just (BothUp below) -> [NamedLevelConstructor t l' sig; projectLevel' l rest]t
                                                     _ -> projectLevel' l rest

data Levels :: Lev m ~> Lev m ~> * where
  InLevel :: Thrist Icelevel l l -> Levels l (1+l)l

t3 :: Thrist Levels 0l 2l
t3 = [InLevel $ projectLevel 0l builtIns, InLevel $ projectLevel 1l builtIns]t

fibrateLevels :: Level l -> Thrist Iceberg () () -> Thrist Levels l a
fibrateLevels l berg = [InLevel $ projectLevel l berg; lazy (fibrateLevels (1+l)l berg)]t


[t30, t31, t32, t33; t34]t = fibrateLevels 0l builtIns
[t40, t41, t42, t43; t44]t = fibrateLevels PolyLevel builtIns
