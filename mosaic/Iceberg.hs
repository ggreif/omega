-- implement the idea described in
-- https://code.google.com/p/omega/wiki/IcebergTypes
-- Omega Impl is here: https://code.google.com/p/omega/source/browse/trunk/tests/Iceberg.prg

{-# LANGUAGE DataKinds, PolyKinds, GADTs, MultiParamTypeClasses, LambdaCase #-}

import Data.Maybe
import Data.Thrist
import GHC.TypeLits
import Unsafe.Coerce (unsafeCoerce)

{-
data kind Multiplicity where
  Mono :: Multiplicity
  Poly :: Multiplicity

data kind Lev (m :: Multiplicity) where
  ValueLevel :: Lev m -- Mono
  LevelUp :: Lev m -> Lev m
  PolyLevel :: Lev m -- Poly -- level n .
-- deriving syntax (lev) Nat(ValueLevel, LevelUp)
-}

-- kind
data Lev where
  ValueLevel :: Lev
  LevelUp :: Lev -> Lev
  PolyLevel :: Lev

data Level :: Lev -> * where
  ValueLevel' :: Level 'ValueLevel
  LevelUp' :: Level l -> Level ('LevelUp l)
  PolyLevel' :: Level 'PolyLevel
-- deriving syntax (l) Nat(ValueLevel, LevelUp)

data Signature :: * where
  Sig :: Signature -- some signature (for now)
  SigCtor :: Sing (t :: Symbol) -> Signature
  SigFun :: Sing (t :: Symbol) -> Signature
  SigVar :: Sing (t :: Symbol) -> Signature
  SigApp :: Signature -> Signature -> Signature

data Iceberg :: * -> * -> * where
  Constructor :: Sing (t :: Symbol) -> Level l -> Signature -> Iceberg () ()

data Icename :: Symbol -> Symbol -> * where -- entities with certain name
  NamedConstructor :: Sing (t :: Symbol) -> Level l -> Signature -> Icename t t

data Icelevel :: Lev -> Lev -> * where -- entities with certain level
  LevelConstructor :: LevelFits l' l => Sing (t :: Symbol) -> Level l -> Signature -> Icelevel l' l'

{-
data kind TagLev :: Multiplicity where
  TL :: Symbol -> Lev m -> TagLev m
-}

-- kind
data TagLev where
  TL :: Symbol -> Lev -> TagLev

data Icenamelevel :: TagLev -> TagLev -> * where -- entities with certain level and name
  NamedLevelConstructor :: LevelFits l' l => Sing (t :: Symbol) -> Level l -> Signature -> Icenamelevel (TL t l') (TL t l')


class LevelFits (l :: Lev) (m :: Lev) -- ~> * -- where

{-


builtIns :: Thrist Iceberg () ()
builtIns = [ Constructor `Z 0l $ SigApp natPrimeCtor (SigCtor `Z)
           , Constructor `S 0l $ SigApp (SigApp varrowCtor (SigApp natPrimeCtor $ SigVar `a)) (SigApp natPrimeCtor $ (SigApp (SigCtor `S) $ SigVar `a))
           , Constructor natPrime 0l $ SigApp (SigApp karrowCtor natCtor) starCtor
           , Constructor `Z 1l $ natCtor
           , Constructor `S 1l $ SigApp (SigApp karrowCtor natCtor) natCtor
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
        starCtor = SigCtor starN
        natPrimeCtor = SigCtor natPrime
        varrowCtor = SigCtor varrow
        karrowCtor = SigCtor karrow
        natCtor = SigCtor `Nat

-}


data Equal :: k -> k -> * where
  Eq :: Equal a a

data Void

sameLabel :: Sing (l :: Symbol) -> Sing (l' :: Symbol) -> Either (Equal l l') (Ordering, Equal l l' -> Void)
sameLabel l l' = case fromSing l `compare` fromSing l of
                 EQ -> Left (unsafeCoerce Eq)
                 other -> Right (other, \case { _ -> undefined }{-FIXME-})

projectName :: Sing (l :: Symbol) -> Thrist Iceberg () () -> Thrist Icename l l
projectName _ Nil = Nil
projectName l (Cons (Constructor l' lev sig) rest) = case l `sameLabel` l' of
                                                Left Eq -> Cons (NamedConstructor l' lev sig) (projectName l rest)
                                                _ -> projectName l rest


{-

projectName' :: Sing (t :: Symbol) -> Thrist Icelevel l l -> Thrist Icenamelevel (TL t l) (TL t l)
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

-}
