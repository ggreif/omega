\begin{code}
module Wrappers where 

import BasicTypes
import BasicTypesUtils 
import qualified Data.Map as Map 
import TcMonad 
import List ( (\\) ) 
import Text.PrettyPrint.HughesPJ 

import qualified Control.Monad as CM 

import TcTerm 

-- handles constructor and environment creation
---------------------------------------------------



tcDecls :: [Decl] -> 
           [Name] ->  -- accumulator of names entering context 
           Tc () 

tcDecls [] _ = return () 

tcDecls ((Data typeName vars ctors):ds) sig_names 
 = do { env <- getTypeNameEnv 
      ; case Map.lookup typeName env of 
          Just _ -> failTc (text "Multiple definition of datatype" <+>
                            vcat [pprName typeName])
          Nothing -> extendTypeNameEnv typeName (length vars) cont }
 where cont = do { cNamesTypes <- mapM ( \(Ctor conName conSigma) -> 
                                   do { env <- getTermEnv
                                      ; case Map.lookup conName env of 
                                          Just _ -> failTc (text "Multiple bindings for constructor" <+> 
                                                            vcat [pprName conName])
                                          Nothing -> 
                                              do {
                                                 ; (_,conTau) <- skolemise conSigma
                                                 ; case splitCType conTau of 
                                                      (_, (Just (n', tyArgs)))  
                                                        | (n' == typeName) && (length tyArgs == length vars) -> 
                                                                    return (conName, conSigma)
                                                      _ -> failTc (text "Constructor does not match datatype declaration" <+> 
                                                                    vcat [pprName conName]) 
                                                  }
                                    } ) ctors 
                 ; extendTermEnvMany cNamesTypes (tcDecls ds sig_names) }

tcDecls ((AnnDef n sigma):ds) sig_names
  = do { env <- getTermEnv 
       ; case Map.lookup n env of 
           Just _ -> failTc (text "Duplicate binding of term" <+> 
                             vcat [pprName n]) 
           Nothing -> extendTermEnv n sigma (tcDecls ds (n:sig_names)) }

tcDecls ((Def n plist term):ds) sig_names 
  = do { env <- getTermEnv
       ; let term' = foldr (\p r -> (Lam p r)) term plist
       ; case Map.lookup n env of 
           Just sigma -> 
               case (filter (\x -> x == n) sig_names)of 
                 [] -> failTc (text "Duplicate binding of term" <+> 
                               vcat [pprName n]) 
                 _ -> -- binding came from signature 
                      do { -- convert it to annotation! 
                         ; checkSigma (Ann term' sigma) sigma 
                         ; printTc $ vcat [text "Checked term:" <+> text n,
                                          text "against type:" <+> ppr sigma]
                         ; tcDecls ds (sig_names \\ [n]) }
           -- infer it 
           Nothing -> -- not in environment 
             do { sigma <- typecheck term' 
                ; printTc $ vcat [text "Inferred for term:" <+> text n, 
                                 text "type was         :" <+> ppr sigma] 
                ; extendTermEnv n sigma $ tcDecls ds sig_names }
   
    }


\end{code} 