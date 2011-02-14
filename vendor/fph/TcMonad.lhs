\begin{code}
module TcMonad where 

import BasicTypes
import BasicTypesUtils 

import qualified Data.Map as Map
import Text.PrettyPrint.HughesPJ
import Data.IORef
import List( nub, (\\) )
import Monad ( foldM ) 
------------------------------------------
--      The monad itself                --
------------------------------------------

data TcEnv 
  = TcEnv { uniqs          :: IORef Uniq,                    -- unique name supply
            var_env        :: Map.Map Name Sigma,            -- type environment for term variables
            types_env      :: Map.Map Name Arity             -- records declared types and their arities 
          }

newtype Tc a = Tc (TcEnv -> IO (Either ErrMsg a))
unTc :: Tc a ->   (TcEnv -> IO (Either ErrMsg a))
unTc (Tc a) = a

type ErrMsg = Doc

instance Monad Tc where
   return x = Tc (\_env -> return (Right x))
   fail err = Tc (\_env -> return (Left (text err)))
   m >>= k  = Tc (\env -> do { r1 <- unTc m env
                             ; case r1 of
                                 Left err -> return (Left err)
                                 Right v  -> unTc (k v) env })


-- running, lifting, warning, debugging, failing 

failTc :: Doc -> Tc a 
failTc d = fail (docToString d)

runTc :: TcEnv -> Tc a -> IO (Either ErrMsg a)
runTc env (Tc tc) = tc env

lift :: IO a -> Tc a
lift st = Tc (\_env -> do { r <- st; return (Right r) })

warnTc :: Doc -> Tc () 
warnTc msg = lift $ putStrLn (docToString (text "WARNING:" <+> msg))

debugTc :: Doc -> Tc () 
debugTc msg = lift $ putStrLn (docToString (text "DEBUG: " <+> msg))

printTc :: Doc -> Tc () 
printTc msg = lift $ putStrLn (docToString msg)

check :: Bool -> Doc -> Tc ()
check True  _ = return ()
check False d = failTc d

createEnv :: [(Name, Sigma)] ->               -- Constructor binds 
             [(Name, Arity)] -> IO TcEnv      -- Type name binds 
createEnv var_binds type_binds 
  = do { ref <- newIORef 0 
       ; let env = TcEnv { uniqs = ref
                         , var_env = Map.fromList var_binds
                         , types_env = Map.fromList type_binds
                         }
       ; return env } 

-- creating and reading tc refs 
newTcRef :: a -> Tc (IORef a)
newTcRef v = lift (newIORef v)

readTcRef :: IORef a -> Tc a
readTcRef r = lift (readIORef r)

writeTcRef :: IORef a -> a -> Tc ()
writeTcRef r v = lift (writeIORef r v)


--------------------------------------------------
--      Dealing with the type environment       --
--------------------------------------------------

extendTermEnv :: Name -> Sigma -> Tc a -> Tc a
extendTermEnv var sigma (Tc m) 
  = Tc (\env -> m (extend env))
  where
    extend env = env { var_env = Map.insert var sigma (var_env env) }

extendTypeNameEnv :: Name -> Arity -> Tc a -> Tc a 
extendTypeNameEnv tn arity (Tc m) 
  = Tc (\env -> m (extend env))
  where
    extend env = env { types_env = Map.insert tn arity (types_env env) }


extendTermEnvMany :: [(Name,Sigma)] -> Tc a -> Tc a 
extendTermEnvMany binds (Tc m)
  = Tc (\env -> m (extend env))
  where 
    extend env = env { var_env = (Map.union (Map.fromList binds) (var_env env)) }


getTermEnv :: Tc (Map.Map Name Sigma)
getTermEnv = Tc (\ env -> return (Right (var_env env)))

lookupAtom :: Name -> Tc Sigma    -- May fail
lookupAtom n 
  = do { env <- getTermEnv
       ; case Map.lookup n env of
           Just mty -> return mty
           Nothing -> failTc (text "Not in scope:" <+> quotes (pprName n)) }

-- type names environment 
getTypeNameEnv :: Tc (Map.Map Name Arity) 
getTypeNameEnv = Tc (\ env -> return (Right (types_env env))) 

lookupTypeName :: Name -> Tc Arity    -- May fail
lookupTypeName n 
  = do { env <- getTypeNameEnv
       ; case Map.lookup n env of
           Just arity -> return arity
           Nothing -> failTc (text "Datatype not declared" <+> quotes (pprName n)) }

----------------------------------------------------
--      Creating, reading, writing MetaTvs        --
----------------------------------------------------

newTyVarTy :: Tc Type
newTyVarTy 
    = do { tv <- newMetaTyVar
         ; return (MetaTv tv) }

createMetaTyVar :: Bool -> Tc MetaTv
createMetaTyVar f 
    = do { uniq <- newUnique                    -- fresh identity
         ; tref <- newTcRef (TyInfo f None)     -- no bounds
         ; return (Meta uniq tref) } 

newMetaTyVar :: Tc MetaTv 
newMetaTyVar = createMetaTyVar False

newMonoTyVar :: Tc MetaTv
newMonoTyVar = createMetaTyVar True 

newSkolemTyVar :: TyVar -> Tc TyVar
newSkolemTyVar tv 
  = do { uniq <- newUnique 
       ; return (SkolemTv (tyVarName tv) uniq) }

readTv  :: MetaTv -> Tc TyInfo
readTv  (Meta _ ref) = readTcRef ref

writeTv :: MetaTv -> TyInfo -> Tc () 
writeTv (Meta _ ref) = writeTcRef ref

newUnique :: Tc Uniq
newUnique = Tc (\ (TcEnv {uniqs = ref}) ->
                    do { uniq <- readIORef ref ;
                       ; writeIORef ref (uniq + 1)
                       ; return (Right uniq) })


------------------------------------------
--    Instantiation & Skolemization     --
------------------------------------------

instantiate :: Sigma -> Tc Rho
instantiate ty = instantiateGetTvs ty >>= return.fst

instantiateGetTvs :: Type -> Tc (Type, [MetaTv])
instantiateGetTvs (ForAll tvs ty) 
  = do { mvs <- mapM (\_ -> newMetaTyVar) tvs
       ; let tys = map MetaTv mvs
       ; return (substTy tvs tys ty, mvs) }
instantiateGetTvs ty = return (ty,[]) 

skolemise :: Sigma -> Tc ([TyVar], Rho)
-- shallow skolemisation 
skolemise (ForAll tvs ty)	
  = do { sks1 <- mapM newSkolemTyVar tvs
       ; (sks2, ty') <- skolemise (substTy tvs (map TyVar sks1) ty)
       ; return (sks1 ++ sks2, ty') }
skolemise ty = return ([], ty)


-------------------------------
--  Monomorphisation         --
-------------------------------                 

-- Boolean flag semantics:
-- True  -> passed under a MetaTv
-- False -> still examining top-level rigid structures 

mkMono :: Bool -> Type -> Tc ()
mkMono f sty@(ForAll _ ty) 
  = do { mkMono f ty 
       ; if f then failTc $ text "Type" <+> ppr sty <+> text "appears in bound of monomorphic variable!"
         else return () } 
mkMono f (Fun arg res) = mkMono f arg >> mkMono f res 
mkMono f (TyCon _ tys) = mapM_ (mkMono f) tys 
mkMono _ (TyVar _)     = return ()
mkMono _ (MetaTv tv) 
  = do { info <- readTv tv
       ; case info of 
           TyInfo True _   -> return () 
           TyInfo False None -> writeTv tv (TyInfo True None) 
           TyInfo False (Flexi (Scheme _ ty)) -> 
             do { ty0 <- instantiate ty
                ; mkMono True ty0
                ; writeTv tv (TyInfo True (Rigid ty0)) }
           TyInfo False (Rigid ty) -> 
             do { mkMono True ty 
                ; writeTv tv (TyInfo True (Rigid ty)) } 
       }


-- Zonking: eliminates any substitution in the type
-- Input type invariants: 
-- (1) must not contain any unresolved flexi constraints
-- (2) must have its escape conditions checked 
-- (3) must have its monomorphism conditions checked 
---------------------------------------------------------
zonkType :: Type -> Tc Type
zonkType (ForAll ns ty) = do { ty' <- zonkType ty 
                             ; return (ForAll ns ty') }
zonkType (Fun arg res)  = do { arg' <- zonkType arg 
                             ; res' <- zonkType res
                             ; return (Fun arg' res') }
zonkType (TyCon tc tys) = do { tys' <- mapM zonkType tys
                             ; return (TyCon tc tys') } 
zonkType (TyVar n)      = return (TyVar n)
zonkType (MetaTv tv)    -- mutable type variable
  = do { mb_ty <- readTv tv
       ; case mb_ty of
           TyInfo _ (None) -> return (MetaTv tv) 
           TyInfo f (Rigid ty) -> 
              do { ty0 <- zonkType ty 
                 ; writeTv tv (TyInfo f (Rigid ty0))
                 ; return ty0 
                 }
           TyInfo _ (Flexi _) -> 
             do { debugTc $ vcat [text "Flexible variable :" <+> ppr (MetaTv tv), 
                                  text "Has flexible bound!" ]
                ; failTc $ text "Bug: unresolved flexible constraints!" }
       }

-- ------------------------------------------
-- --      Quantification                  --
-- ------------------------------------------

quantify :: [MetaTv] -> Rho -> Tc Sigma

-- Quantify over the specified type variables. 
-- The invariant is that all these variables have empty bindlists
quantify tvs ty
  = do { ty0 <- zonkType ty
       ; let nb = new_bndrs ty0
       ; mapM_ bind (tvs `zip` nb)
       ; ty1 <- zonkType ty0
       ; case nb of 
           [] -> return ty1 
           _ ->  return (ForAll nb ty1) }
  where
    new_bndrs s = take (length tvs) (allBinders \\ (tyVarBndrs s))
    bind (tv, name) = writeTv tv (TyInfo True (Rigid (TyVar name))) 

    tyVarBndrs :: Tau -> [TyVar]
    tyVarBndrs = nub.bndrs
        where
          bndrs (ForAll vrs body) = vrs ++ bndrs body
          bndrs (Fun arg res)     = (bndrs arg) ++ (bndrs res) 
          bndrs (TyCon _ stys)    = nub $ concat (map bndrs stys)
          -- even for meta-variables, their type bounds 
          -- are zonked out at this point
          bndrs _                 = [] 

allBinders :: [TyVar] -- a,b,..z, a1, b1,... z1, a2, b2,... 
allBinders =  [ BoundTv [x]          | x <- ['a'..'z'] ] ++
              [ BoundTv (x : show i) | i <- [1 :: Integer ..], x <- ['a'..'z']]


-- ------------------------------------------
-- --      Getting the free tyvars         --
-- ------------------------------------------

-- all possible meta type variables mentioned in a type and its bounds 
metaTvs :: [Type] -> Tc [MetaTv]
metaTvs tys = foldM go [] tys
  where 
    go :: [MetaTv] -> Type -> Tc [MetaTv]
    go acc (MetaTv tv) 
	| tv `elem` acc    = return acc
	| otherwise        =
            do { ref <- readTv tv
               ; case ref of 
                   TyInfo _ (None)     -> return (tv:acc)
                   TyInfo _ (Rigid ty) -> go (tv:acc) ty 
                   TyInfo _ (Flexi (Scheme vrs ty)) -> 
                      do { bvars <- go (tv:acc) ty
                         ; return (bvars \\ vrs) }
               }
    go acc (TyVar _)       = return acc
    go acc (TyCon _ taus)  = foldM go acc taus
    go acc (Fun arg res)   = go acc res >>= \acc0 -> go acc0 arg
    go acc (ForAll _ ty)   = go acc ty

-- all possible variables (bound or skolems) mentioned in a type and its bounds
freeTyVars :: [Type] -> Tc [TyVar]
freeTyVars tys = foldM (go []) [] tys
  where 
    go :: [TyVar] -- Ignore occurrences of bound type variables
       -> [TyVar] -- Accumulates result
       -> Type    -- Type to look at
       -> Tc [TyVar]
    go bnd acc (TyVar tv)
	| tv `elem` bnd         = return acc
	| tv `elem` acc           = return acc
        | otherwise               = return (tv:acc)
    go bnd acc (MetaTv tv) = 
        do { ref <- readTv tv
               ; case ref of 
                   TyInfo _ (None)     -> return acc
                   TyInfo _ (Rigid ty) -> go bnd acc ty 
                   TyInfo _ (Flexi (Scheme _ ty)) -> go bnd acc ty
               }
    go bnd acc (TyCon _ taus)   = foldM (go bnd) acc taus
    go bnd acc (Fun arg res)    = (go bnd acc res) >>= \acc0 -> go bnd acc0 arg
    go bnd acc (ForAll tvs ty)  = go (tvs ++ bnd) acc ty


getEnvTypes :: Tc [Type]
  -- Get the types mentioned in the environment
getEnvTypes = do { tm_env <- getTermEnv
                 ; return $ (Map.elems tm_env) } 

-- returns the reachable unification variables of a type
-- [WARNING: if you want a small list back, make sure you zonk/solve the type first!]
getMetaTyVars :: [Type] -> Tc [MetaTv]
getMetaTyVars = metaTvs

-- returns a number of free variables, through the constraints
getFreeTyVars :: [Type] -> Tc [TyVar]
getFreeTyVars = freeTyVars


fcv :: [Type] -> Tc [MetaTv]
fcv tys = foldM go [] tys
  where 
    go :: [MetaTv] -> Type -> Tc [MetaTv]
    go acc (MetaTv tv)     = return (tv:acc)
    go acc (TyVar _)       = return acc
    go acc (TyCon _ taus)  = foldM go acc taus
    go acc (Fun arg res)   = go acc res >>= \acc0 -> go acc0 arg
    go acc (ForAll _ ty)   = go acc ty

\end{code}
