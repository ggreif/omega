\begin{code}
module BasicTypes where

-- This module defines the basic types used by the type checker
-- Everything defined in here is exported
import Data.IORef

infixr 4 -->     -- The arrow type constructor
infixl 4 `App`   -- Application

-----------------------------------
--      Ubiquitous types        -- 
-----------------------------------

type Name   = String    -- names are very simple
type TyName = String    -- names for types, such as Bool, Int, List etc 

-- declarations and constructors 
type Arity = Int 

data Decl = Data TyName [Name] [Ctor]  -- name, arity vars, constructors
          | AnnDef Name Sigma 
          | Def Name [Pattern] Term 

data Ctor = Ctor Name Sigma


-----------------------------------
--      Expressions             -- 
-----------------------------------
                                       -- Examples below
data Term = Var Name                    -- x
          | Con Name                    -- C 
          | Lit Int                     -- 3
          | App Term Term               -- e1 e2 
          | Lam Pattern Term            -- \p -> e
          | Let Name Term Term          -- let x = u in e 
          | AnnLet Name Sigma Term Term -- let x :: sigma = u in e 
          | Ann Term Sigma              -- (e :: sigma) 
          | Case Term [(Pattern,Term)]  -- case e of { ... } 

atomicTerm :: Term -> Bool
atomicTerm (Var _) = True
atomicTerm (Lit _) = True
atomicTerm (Con _) = True 
atomicTerm _       = False

-- Patterns                    
data Pattern = PAny                  -- _ 
             | PVar Name             -- x 
             | PCon Name [Pattern]   -- C x1 x2 
             | PAnn Pattern Sigma    -- (x::sigma) 

-- Types 
type Sigma = Type
type Rho   = Type 
type Tau   = Type

data Type  = ForAll [TyVar] Rho  
	   | Fun Sigma Sigma    	 
	   | TyCon TyName [Sigma] 
	   | TyVar TyVar          -- always bound by a forall 
           | MetaTv MetaTv        -- meta type variables

data TyVar = BoundTv String
           | SkolemTv String Uniq -- skolems 

data MetaTv = Meta Uniq TyRef

-- schemes quantified over their constraint part 
data Scheme = Scheme [MetaTv] Type 

{--------------------------- Definitions  -------------------------} 
{- ``Monomorphic type'': 
      o A type consisting only of constructors and 
        ``monomorphic variables'' (no foralls). 
 - ``Monomorphic variable'': 
      o A MetaTv that has mono = True
 ------------------------------------------------------------------}

-- Flexible or rigid bounds 
data Bound 
  = Flexi Scheme -- Flexi ty => variable must be instance of ty 
  | Rigid Type   -- Rigid ty => variable must be equal to ty 
  | None         -- Stil unified variable

-- Information about a constrained variable 
data TyInfo = TyInfo { mono  :: Bool     -- must be monomorphic?  
                     , bound :: Bound    -- flexible or rigid bound 
                     }

{-------------------------- Invariants ----------------------------} 
{- In a bound (Flexi ty), all MetaTvs of ty are monomorphic 

 - In a TyInfo, if mono = True, then bound is either (Rigid ty), 
   where ty is monomorphic, or None 
 ------------------------------------------------------------------}

type TyRef = IORef TyInfo 

instance Eq MetaTv where
  (Meta u1 _) == (Meta u2 _) = u1 == u2

instance Eq TyVar where
  (BoundTv s1)    == (BoundTv s2)    = s1 == s2
  (SkolemTv _ u1) == (SkolemTv _ u2) = u1 == u2
  _ == _ = False 

type Uniq = Int

-- Some constructors 
(-->) :: Sigma -> Sigma -> Sigma
arg --> res = Fun arg res

intType, boolType :: Tau
intType  = TyCon "Int" []
boolType = TyCon "Bool" []

type Env = [(TyVar, Tau)]

\end{code}