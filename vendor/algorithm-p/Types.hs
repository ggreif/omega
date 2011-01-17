-- Time-stamp: <2010-05-13 23:35:27 cklin>

module Types where

import Control.Monad (guard)
import Data.List ((\\), intercalate, nub)
import qualified Data.Map as Map

import Common

--------- Program abstract syntax tree types

type Ident = String
type Branch = (Pat, Term)

data Term
    = Var Ident
    | Con String
    | Int Integer
    | App Term Term
    | Lam Ident Term
    | Let [(Ident, Term)] Term
    | Case Term [Branch]
      deriving (Eq, Show)

data Pat
    = PatCon String [Ident]
    | PatInt Integer
      deriving Eq

data Type
    = TyVar Ident
    | TyCon String [Type]
    | TyMeta Int
    | TySkol Int
      deriving Eq

data Data
    = Data String [Ident]
      deriving (Eq, Show)

data Cons
    = Cons String Type
      deriving (Eq, Show)

data Program
    = Value Ident Term
    | Decl Data [Cons]
    | Info [String]
      deriving (Eq, Show)

--------- Lexical analyzer token types

data Terminal
    = LexOp             -- +
    | LexDef            -- =
    | LexArr            -- ->
    | LexLam            -- \
    | LexSemi           -- ;
    | LexComa           -- ,
    | LexType           -- ::
    | LexParL           -- (
    | LexParR           -- )
    | LexBraL           -- {
    | LexBraR           -- }
    | LexVar Ident      -- identifier
    | LexCon String     -- Constructor
    | LexInt Integer    -- 42
    | LexData           -- data  (keyword)
    | LexWhere          -- where (keyword)
    | LexCase           -- case  (keyword)
    | LexOf             -- of    (keyword)
    | LexLet            -- let   (keyword)
    | LexIn             -- in    (keyword)
    | LexNext
    | LexDoc String
    | LexError
      deriving (Eq, Show)

--------- Type inference engine data structures

type Subst  = Map.Map Int Type
type Rename = Map.Map Int Int
type Type2  = (Type, Type)

-- The (polymorphic) variable types and the (polymorphic) data
-- constructor types no longer contain a list of their free type
-- variables because the list is easily reconstructed with freeType.

data VarTy  = VarTy Type
data ConsTy = ConsTy Type

type VarE   = Map.Map Ident VarTy
type ConsE  = Map.Map String ConsTy

mapVarE :: Endo Type -> Endo VarE
mapVarE = Map.map . mapVarTy

mapVarTy :: Endo Type -> Endo VarTy
mapVarTy f (VarTy t) = VarTy (f t)

--------- Frequently used types

botType       = TyVar "a"
intType       = TyCon "Int" []
arrType t1 t2 = TyCon "->"  [t1, t2]
plusType      = arrType intType (arrType intType intType)
tupleType     = arrType varx (arrType vary tuple)
    where tuple = TyCon "," [varx, vary]
          varx  = TyVar "x"
          vary  = TyVar "y"

--------- General type utility functions

metaP :: Type -> Bool
metaP (TyMeta _) = True
metaP _ = False

consP :: Type -> Bool
consP (TyCon _ _) = True
consP _ = False

deCons :: [Type] -> Maybe (String, [[Type]])
deCons tx =
    let consTc (TyCon tc _) = tc
        consAx (TyCon _ ax) = ax
    in do guard (tx /= [])
          guard (all consP tx)
          guard (same (map consTc tx))
          return (consTc (head tx), map consAx tx)

-- Collect free or meta type variables in either a type or a type
-- environment.

collectType :: Eq a => Endo (Type -> [a])
collectType f = walk where
    walk (TyCon _ tas) = unions (map walk tas)
    walk t             = f t

freeType :: Type -> [Ident]
freeType = collectType free where
    free (TyVar tv) = [tv]
    free _          = []

skolType :: Type -> [Int]
skolType = collectType skol where
    skol (TySkol idx) = [idx]
    skol _            = []

skolTypes :: [Type] -> [Int]
skolTypes = unionMap skolType

metaType :: Type -> [Int]
metaType = collectType meta where
    meta (TyMeta idx) = [idx]
    meta _            = []

metaTypes :: [Type] -> [Int]
metaTypes = unionMap metaType

metaVarE :: VarE -> [Int]
metaVarE = unionMap (metaType . unwrap) . Map.elems
    where unwrap (VarTy t) = t

-- Separate the type of a user-defined data constructor into a list of
-- argument types and the range type.  Used in pattern matching.

spine :: Type -> ([Type], Type)
spine = walk [] where
    walk ax (TyCon "->" [t1, t2]) = walk (t1:ax) t2
    walk ax t =
        if consP t then (reverse ax, t)
        else bug "Malformed data constructor type"

-- Check if a meta type variable appears in multiple elements of the
-- list of types.  Multiple occurrences in one element does not count.

multiP :: [Type] -> Int -> Bool
multiP tx = flip elem multi where
    skol = concat (map skolType tx)
    meta = concat (map metaType tx)
    tvs = meta ++ skol
    multi = nub (tvs \\ nub tvs)

--------- Pretty-printing types and constraints

instance Show Pat where
    show (PatCon "," ax) = paren (intercalate ", " ax)
    show (PatCon tc ax)  = unwords (tc:ax)
    show (PatInt i)      = show i

instance Show Type where
    show = showType

showType (TyVar tv)   = tv
showType (TyMeta idx) = '?' : show idx
showType (TySkol idx) = '!' : show idx
showType (TyCon "->" [t1, t2]) =
    unwords [showType1 t1, "->", showType t2]
showType (TyCon "," [t1, t2]) =
    paren (concat [showType1 t1, ", ", showType t2])
showType (TyCon tc ax) =
    unwords (tc : map showType2 ax)

paren :: String -> String
paren str = concat ["(", str, ")"]

showType1 t@(TyCon "->" _) = paren (showType t)
showType1 t = showType t

showType2 t@(TyCon "," _) = showType t
showType2 t@(TyCon _ (_:_)) = paren (showType t)
showType2 t = showType1 t

showLocal :: (Ident, VarTy) -> String
showLocal (x, vt) = unwords [x, "::", show vt]

instance Show VarTy where
    show (VarTy t) = showPolyType t

instance Show ConsTy where
    show (ConsTy t) = showPolyType t

showPolyType t = quant ++ show t where
    btvx = freeType t
    only ax s = if null ax then "" else s
    quant = only btvx (unwords ("forall" : btvx) ++ ". ")

