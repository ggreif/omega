-- Copyright (c) Gabor Greif
-- OGI School of Science & Engineering, Oregon Health & Science University
-- Maseeh College of Engineering, Portland State University
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Tue Nov 7 15:20:11 Middle European Time 2007
-- Omega Interpreter: version 1.4.2+


module GenLLVM(genLLVM) where
import Syntax
import Encoding2(to)
import Monads(Exception(..), FIO(..),unFIO,handle,runFIO,fixFIO,fio,
              write,writeln,HasNext(..),HasOutput(..))
import Bind

data Thrist :: (* -> * -> *)  -> * -> * -> * where
  Nil :: Thrist k a a
  Cons :: k c b -> Thrist k b a -> Thrist k c a

-- Thrist appending

appendThrist :: Thrist b c d ->
		Thrist b d e ->
		Thrist b c e

appendThrist Nil a = a
appendThrist (Cons b r) a = Cons b (appendThrist r a)



genLLVM :: Ev -> Exp -> FIO V
genLLVM geh ex = do
		 tree <- toLLVM ex
		 text <- showThrist tree
		 return (to text)


-- declare some phantoms

data Term -- terminator
data Cabl -- continuable
data Oper = OLt | OLe | OGt | OGe | OEq | ONe

instance Show Oper where
  show OLt = "lt"
  show OLe = "le"
  show OGt = "gt"
  show OGe = "ge"
  show OEq = "eq"
  show ONe = "ne"

data Instr :: * -> * -> * where
  -- Terminators
  Unwind :: Instr a Term
  Branch :: BasicBlock -> Instr a Term
  Return :: Value -> Instr Cabl Term
  --Switch :: Value {-(LInt bits)-} -> BasicBlock {-t Normal d1-} -> [(Value, BasicBlock {-t Normal d2-})] -> Instr a Term
  Switch :: Value -> [(Value, BasicBlock)] -> Instr Cabl Term
  Unreachable :: Instr Cabl Term
  -- Value generators
  Add :: Value -> Value -> Instr Cabl Cabl
  Sub :: Value -> Value -> Instr Cabl Cabl
  Mul :: Value -> Value -> Instr Cabl Cabl
  Div :: Value -> Value -> Instr Cabl Cabl
  Icmp :: Oper -> Value -> Value -> Instr Cabl Cabl
  -- Special values
  Phi :: [(Value, BasicBlock)] -> Instr Cabl Cabl
  Def :: Name -> Instr a b -> Instr a b

type LType = String

data BasicBlock :: * where
  BB :: Name -> Thrist Instr Cabl Term -> BasicBlock

data Value :: * where
  LLit :: Lit -> Value
  Undef :: LType -> Value
  Ref :: LType -> Name -> Value
  Lab :: Name -> Value

toLLVM :: Exp -> FIO (Thrist Instr Cabl Term)
toLLVM (Lit x) = return (Cons (Return $ LLit x) Nil)
toLLVM (App f x) = do
		   let cont = \val -> return $ Cons (Return $ val) Nil
		   subApplication name1 f [x] cont
toLLVM c@(Case _ _) = subComp name1 c (\val -> return $ Cons (Return $ val) Nil)
toLLVM something = fail ("cannot toLLVM: " ++ show something)

type FIOTerm = FIO (Thrist Instr Cabl Term)
type FIOTermCont = Value -> FIOTerm

subComp :: Name -> Exp -> FIOTermCont -> FIOTerm
subComp _ (Lit x) cont = cont $ LLit x
subComp lab (App f x) cont = subApplication lab f [x] cont
--subComp lab (Case e ms) = subCase lab e ms
subComp lab e cont = fail ("cannot subComp: " ++ show lab ++ " = " ++ show e)


caseArm :: BasicBlock -> Match Pat Exp Dec -> FIO (Value, Either BasicBlock Value)
caseArm cont (_, Plit (i@(Int _)), Normal (Lit (j@(Int _))), decs) = return (LLit i, Right (LLit j))

mapFIO :: (a -> FIO b) -> [a] -> FIO [b]
mapFIO f [] = return []
mapFIO f (a:as) = do { fa <- f a; fas <- mapFIO f as; return (fa:fas) }

zipWithFIO :: (a -> b -> FIO c) -> [a] -> [b] -> FIO [c]
zipWithFIO f (a:as) (b:bs) = do { fc <- f a b; fcs <- zipWithFIO f as bs; return (fc:fcs) }
zipWithFIO _ _ _ = return []

splitArms :: [Match Pat Exp Dec] -> FIO [(Value, BasicBlock)]
splitArms matches = do { arms' <- arms; landings' <- landings; zipWithFIO assembleStartLand arms' landings' }
    where arms = do { phiBB <- phiBB; mapFIO (caseArm phiBB) matches }
	  phi = do { landings <- landings; return $ Phi landings }
	  phiBB :: FIO BasicBlock
	  phiBB = do { n <- fresh; phi' <- phi; return $ BB n (Cons phi' (Cons GenLLVM.Unreachable Nil)) }
	  landings = do { arms <- arms; mapFIO buildLanding arms }
	  buildLanding (val, Right res) = do { phiBB <- phiBB; n <- fresh; return (res, BB n (Cons (Branch phiBB) Nil)) }
	  assembleStartLand (v, Right _) (LLit _, land) = return (v, land)

subCase :: Name -> Exp -> [Match Pat Exp Dec] -> FIO (Thrist Instr Cabl Term, Value)
--subCase lab _ _ = return (Cons (Def lab $ Phi []) Nil, Ref "typ" lab)
--subCase lab (Lit (n@(Int _))) cases = return (Case (LLit n) (map caseArm cases))
subCase lab (Lit (n@(Int _))) cases = do { arms <- splitArms cases; return (Cons (Switch (LLit n) arms) Nil, Ref "i32" lab) }

subApplication :: Name -> Exp -> [Exp] -> FIOTermCont -> FIOTerm
subApplication lab (Reify s (Vlit c)) args _ = fail ("cannot subApplication: ReifyVlit " ++ show s ++ "  " ++ show c)
subApplication lab (Reify s v) args cont = subPrimitive lab s args v cont
--subApplication lab (Lit (CrossStage v)) args = subPrimitive lab v args
subApplication lab (App f x) args cont = subApplication lab f (x:args) cont
subApplication lab fun args _ = fail ("cannot subApplication: " ++ show fun ++ "   args: " ++ show args)

subPrimitive :: Name -> String -> [Exp] -> V -> FIOTermCont -> FIOTerm
subPrimitive lab "<" [a1, a2] _ cont = binaryPrimitive lab (Icmp OLt) "i1" a1 a2 cont
subPrimitive lab "<=" [a1, a2] _ cont = binaryPrimitive lab (Icmp OLe) "i1" a1 a2 cont
subPrimitive lab ">=" [a1, a2] _ cont = binaryPrimitive lab (Icmp OGe) "i1" a1 a2 cont
subPrimitive lab ">" [a1, a2] _ cont = binaryPrimitive lab (Icmp OGt) "i1" a1 a2 cont
subPrimitive lab "==" [a1, a2] _ cont = binaryPrimitive lab (Icmp OEq) "i1" a1 a2 cont
subPrimitive lab "/=" [a1, a2] _ cont = binaryPrimitive lab (Icmp ONe) "i1" a1 a2 cont

subPrimitive lab "+" [a1, a2] _ cont = binaryPrimitive lab Add "i32" a1 a2 cont
subPrimitive lab "-" [a1, a2] _ cont = binaryPrimitive lab Sub "i32" a1 a2 cont
subPrimitive lab "*" [a1, a2] _ cont = binaryPrimitive lab Mul "i32" a1 a2 cont
subPrimitive lab "div" [a1, a2] _ cont = binaryPrimitive lab Div "i32" a1 a2 cont

subPrimitive lab prim args (Vprimfun s f) cont = fail ("cannot subPrimitive, Vprimfun: " ++ show prim ++ "   args: " ++ show args ++ "   s: " ++ s {-++ "   f: " ++ show f-})
subPrimitive lab prim args v cont = fail ("cannot subPrimitive: " ++ show prim ++ "   args: " ++ show args ++ "   v: " ++ show v)

binaryPrimitive :: Name -> (Value -> Value -> Instr Cabl Cabl) -> LType
		-> Exp -> Exp -> FIOTermCont -> FIOTerm
binaryPrimitive lab former typ a1 a2 cont = do
				       l1 <- fresh
				       l2 <- fresh
				       subComp l1 a1 (\v1 ->
						      subComp l2 a2 (\v2 -> do
								     tail <- cont $ Ref typ lab
								     return $ Cons (Def lab $ former v1 v2) tail))


showThrist :: Thrist Instr a Term -> FIO String
showThrist Nil = return ""
showThrist (Cons (Def l i) r) = do
				humpti <- showThrist (Cons i r)
				return (" %" ++ show l ++ " =" ++ humpti)
showThrist (Cons Unwind r) = do
			     humpti <- showThrist r
			     return (" unwind\n" ++ humpti)
showThrist (Cons (Return v) r) = do
				 humpti <- showThrist r
				 return (" return " ++ show v ++ "\n" ++ humpti)

showThrist (Cons i@(Add v1 v2) r) = showBinaryArithmetic "add" v1 v2 i r
showThrist (Cons i@(Sub v1 v2) r) = showBinaryArithmetic "sub" v1 v2 i r
showThrist (Cons i@(Mul v1 v2) r) = showBinaryArithmetic "mul" v1 v2 i r
showThrist (Cons i@(Div v1 v2) r) = showBinaryArithmetic "div" v1 v2 i r
showThrist (Cons i@(Icmp o v1 v2) r) = showBinaryArithmetic ("icmp " ++ show o) v1 v2 i r
showThrist (Cons (Phi _) r) = do
			      humpti <- showThrist r
			      return (" phi xxxx" ++ "\n" ++ humpti)
showThrist (Cons x r) = return "cannot showThrist"

showBinaryArithmetic :: String -> Value -> Value -> Instr a b -> Thrist Instr b Term -> FIO String
showBinaryArithmetic op v1 v2 _ r = do
				    humpti <- showThrist r
				    return (" " ++ op ++ " " ++ show v1 ++ " " ++ show v2 ++ "\n" ++ humpti)

instance Show Value where
  show (LLit (Int i)) = "i32 " ++ show i
  show (Undef t) = t ++ " undef"
  show (Ref t l) = t ++ " %" ++ show l
  show (Lab r) = "label %" ++ show r


