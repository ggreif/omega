-- Time-stamp: <2010-04-01 14:27:11 cklin>

module Main where

import Control.Monad (unless)
import Data.List (partition)
import Data.Maybe (isJust)
import qualified Data.Map as Map

import Common
import Types
import Front
import Monad
import Inference

---------

type IdentType = (Ident, [String], Maybe Type)

makeConsE :: Program -> ConsE
makeConsE (Decl _ cx) = toMap cons where
    tuple = (",", ConsTy tupleType)
    unit  = ("()", ConsTy (TyCon "()" []))
    cons  = unit : tuple : map make cx
    make (Cons dc t) = (dc, ConsTy t)

inferPrograms :: [Program] -> [IdentType]
inferPrograms px =
    let (dx, vx) = partition declP px
        consE = Map.unions (map makeConsE dx)
    in runTi (mapM (inferProgram consE) vx) 1

inferProgram :: ConsE -> Program -> Ti IdentType
inferProgram _ (Info doc) =
    return ("Doc", doc, Nothing)
inferProgram consE (Value x e) =
    do let let_e = Let [(x, e)] (Var x)
       (w, mt) <- arrestTi (inferTop consE let_e)
       return (x, w, mt)

declP :: Program -> Bool
declP (Decl _ _) = True
declP _ = False

---------

printIT :: IdentType -> IO ()
printIT (x, w, Nothing) =
    do let oops = "Type inference failed for " ++ x
       unless (x == "Doc") (putStrLn oops)
       putStrLn (unlines w)
printIT (x, w, Just _) =
    do putStrLn (last w)
       putStrLn (unlines $ init w)

main :: IO ()
main = do p <- parseFile "Examples.lhs"
          mapM_ printIT (inferPrograms p)

