-- Copyright (c) Gabor Greif
-- email ggreif gmail com
-- Subject to conditions of distribution and use; see LICENSE.txt for details.
-- Tue Nov 7 15:20:11 Middle European Time 2007
-- Omega Interpreter: version 1.4.2+


module GenLLVM(genLLVM) where
import Syntax
import Encoding2(to)
import Monads(Exception(..), FIO(..),unFIO,handle,runFIO,fixFIO,fio,
              write,writeln,HasNext(..),HasOutput(..),HasIORef(..))
import Bind
import Control.Monad.Fix

instance MonadFix FIO where
  mfix = fixFIO


data Thrist :: (* -> * -> *)  -> * -> * -> * where
  Nil :: Thrist k a a
  Cons :: k c b -> Thrist k b a -> Thrist k c a

-- Thrist appending

appendThrist :: Thrist b c d ->
                Thrist b d e ->
                Thrist b c e

appendThrist Nil a = a
appendThrist (Cons b r) a = Cons b (appendThrist r a)

-- Thrist extending

extendThrist :: Thrist b c d ->
                b d e ->
                Thrist b c e

extendThrist Nil a = Cons a Nil
extendThrist (Cons b r) a = Cons b $ extendThrist r a




genLLVM :: Ev -> Exp -> FIO V
genLLVM geh ex = do
                 tree <- toLLVM ex
                 text <- showThrist tree
                 return (to text)


-- declare some phantoms

data Term -- terminator
data Cabl -- continuable

data Z
data S n

-- comparison codes
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
  -- Allocation
  Malloc :: LType a -> Value -> Instr Cabl Cabl
  Load :: Value -> Instr Cabl Cabl
  Store :: Value -> Value -> Instr Cabl Cabl
  -- Special values
  Phi :: [(Value, BasicBlock)] -> Instr Cabl Cabl
  Def :: Name -> Instr a b -> Instr a b   -- name instruction result
  Gep :: LType a -> Thrist Gup (a, S Z) (b, Z) -> Value {-a-} -> Instr Cabl Cabl

-- thrist based Gep: eat our own dogfood
data Gup :: * -> * -> * where
  Deref :: Value -> Gup ([a], S d) (a, Z)
  Skip :: Gup (LStruct (a, b), d) (LStruct b, Z)
  Drill :: Gup (LStruct (a, b), d) (a, Z)
  Pick :: Value -> Gup (LArray a, d) (a, Z)

deref0 = Deref (LLit $ Int 0)

data LStruct a
data LArray a

data LType :: * -> * where
  LInt :: Int -> LType Int
  LPtr :: LType a -> LType [a]
  -- Structs
  LEmpty :: LType (LStruct ())
  LExtend :: LType a -> LType (LStruct b) -> LType (LStruct (a, b))
  LArray :: LType a -> Int -> LType (LArray a)
  LNamed :: LType a -> Name -> LType a

i1 = LInt 1
i8 = LInt 8
i32 = LInt 32

data BasicBlock :: * where
  BB :: Name -> Thrist Instr Cabl Term -> BasicBlock

data Value :: * where
  LLit :: Lit -> Value
  Undef :: LType a -> Value
  Ref :: LType a -> Name -> Value  -- refer to named result
  Lab :: Name -> Value

toLLVM :: Exp -> FIO (Thrist Instr Cabl Term)
toLLVM (Lit x) = return (Cons (Return $ LLit x) Nil)
toLLVM (App f x) = do
                   let cont = \val -> return $ Cons (Return $ val) Nil
                   subApplication f [x] cont
toLLVM c@(Case _ _) = subComp c (\val -> return $ Cons (Return $ val) Nil)
toLLVM something = fail ("cannot toLLVM: " ++ show something)

type FIOTerm = FIO (Thrist Instr Cabl Term)
type FIOTermCont = Value -> FIOTerm

subComp :: Exp -> FIOTermCont -> FIOTerm
subComp (Lit x) cont = cont $ LLit x
subComp (App f x) cont = subApplication f [x] cont
subComp (Case e ms) cont = subCase e ms cont
subComp e cont = fail ("cannot subComp: " ++ show e)


caseArm :: BasicBlock -> Match Pat Exp Dec -> FIO (Value, Either (Value, BasicBlock) Value)
caseArm _ (_, Plit (i@(Int _)), Normal (Lit (j@(Int _))), decs) = return (LLit i, Right (LLit j))
caseArm next (_, Plit (i@(Int _)), Normal exp, decs) = do
        capturer <- newRef Nothing
        let cont v = do { () <- writeRef capturer $ Just v; return $ Cons (Branch next) Nil }
        thr <- subComp exp cont
        bbn <- fresh
        let bb = BB bbn thr
        Just captured <- readRef capturer
        return (LLit i, Left (captured, bb))

caseArm next (_, Pcon (Global "Nothing") [], Normal exp, decs) = do
        capturer <- newRef Nothing
        let cont v = do { () <- writeRef capturer $ Just v; return $ Cons (Branch next) Nil }
        thr <- subComp exp cont
        bbn <- fresh
        let bb = BB bbn thr
        Just captured <- readRef capturer
        return (LLit $ Int nothingTag, Left (captured, bb))

mapFIO :: (a -> FIO b) -> [a] -> FIO [b]
mapFIO f [] = return []
mapFIO f (a:as) = do { fa <- f a; fas <- mapFIO f as; return (fa:fas) }

zipWithFIO :: (a -> b -> FIO c) -> [a] -> [b] -> FIO [c]
zipWithFIO f (a:as) (b:bs) = do { fc <- f a b; fcs <- zipWithFIO f as bs; return (fc:fcs) }
zipWithFIO _ _ _ = return []



splitArms :: [Match Pat Exp Dec] -> FIOTermCont -> FIO [(Value, BasicBlock)]
splitArms matches cont = do { (arms, landings) <- magic; zipWithFIO assembleStartLand arms landings }
    where magic :: FIO ([(Value, Either (Value, BasicBlock) Value)], [(Value, BasicBlock)])
          magic = mdo
                  arms <- mapFIO (caseArm bb) matches
                  landings <- mapFIO (buildLanding bb) arms
                  let phi = Phi landings
                  vn <- fresh
                  tail <- cont $ Ref i32 vn
                  n <- fresh
                  let bb = BB n (Cons (Def vn phi) tail)
                  return (arms, landings)
          buildLanding bb (val, Right res) = do { n <- fresh; return (res, BB n (Cons (Branch bb) Nil)) }
          buildLanding bb (val, Left pad) = return pad
          assembleStartLand (v, _) (_, land) = return (v, land)


tagStru = LExtend (LInt 8) LEmpty
tagPtr = LPtr tagStru

justStru = LExtend (LInt 8) (LExtend (LInt 32) LEmpty)
justPtr = LPtr justStru

subCase :: Exp -> [Match Pat Exp Dec] -> FIOTermCont -> FIOTerm
subCase (Lit (n@(Int _))) cases cont = do
                                       arms <- splitArms cases cont
                                       return $ Cons (Switch (LLit n) arms) Nil

subCase (stuff@(Reify s v)) cases cont = do
        fail ("subCase (Reify): " ++ show stuff)
subCase (stuff@(App s v)) cases cont = do
        subComp stuff (\v -> do
                          let tag = Gep justPtr (Cons deref0 $ Cons Drill Nil) v
                          dn <- fresh
                          let dv = Def dn tag
                          ln <- fresh
                          let load = Def ln $ Load (Ref (LPtr i8) dn)
                          arms <- splitArms cases cont
                          return $ Cons dv $ Cons load $ Cons (Switch (Ref i8 ln) arms) Nil)
subCase stuff cases cont = do
        fail ("subCase: " ++ show stuff)

subApplication :: Exp -> [Exp] -> FIOTermCont -> FIOTerm
subApplication (Reify s (Vlit c)) args _ = fail ("cannot subApplication: ReifyVlit " ++ show s ++ "  " ++ show c)
subApplication (Reify s v) args cont = subPrimitive s args v cont
--subApplication (Lit (CrossStage v)) args = subPrimitive v args
subApplication (App f x) args cont = subApplication f (x:args) cont
subApplication fun args _ = fail ("cannot subApplication: " ++ show fun ++ "   args: " ++ show args)

data Initer :: * -> * -> * where
  IMake :: LType (LStruct (a, b)) -> Initer () [LStruct (a, b)]
  ITag :: Int -> Initer [LStruct (a, b)] (LStruct b)
  ISlot :: Value -> Initer (LStruct (b, c)) (LStruct c)

type InitHeap a = Thrist Initer [a] (LStruct ())
type AllocAndInitHeap = Thrist Initer () (LStruct ())

fillSlots :: LType [LStruct (a, b)] -> InitHeap (LStruct (a, b)) -> Value -> FIOTermCont -> FIOTerm
fillSlots (typ@(LPtr str)) fill obj cont = gepAndStore str (Cons deref0 Nil) typ fill obj cont
    where gepAndStore :: LType (LStruct c)
                      -> Thrist Gup ([LStruct (a, b)], S Z) (LStruct c, Z)
                      -> LType [LStruct (a, b)]
                      -> Thrist Initer d (LStruct ())
                      -> Value
                      -> FIOTermCont -> FIOTerm
          gepAndStore LEmpty thr typ Nil obj cont = do
              cont obj
          gepAndStore (LExtend here more) thr typ (Cons (ISlot val) rest) obj cont = do
              l <- fresh
              let gep = Def l $ Gep typ (extendThrist thr Drill) obj
              let store = Store val $ Ref (LPtr here) l
              tail <- gepAndStore more (extendThrist thr Skip) typ rest obj cont
              return $ Cons gep $ Cons store tail
          gepAndStore (LExtend here more) thr typ (Cons (ITag tag) rest) obj cont = do
              l <- fresh
              let gep = Def l $ Gep typ (extendThrist thr Drill) obj
              let store = Store (LLit $ Int tag) $ Ref (LPtr here) l
              tail <- gepAndStore more (extendThrist thr Skip) typ rest obj cont
              return $ Cons gep $ Cons store tail

allocSlots :: AllocAndInitHeap -> FIOTermCont -> FIOTerm
allocSlots (Cons (IMake typ) fill) cont = do
        let ptyp = LPtr typ
        lab <- fresh
        tail <- fillSlots ptyp fill (Ref ptyp lab) cont
        return $ Cons (Def lab $ Malloc typ singleObj) tail


justTag = 3
justAllocator :: Value -> AllocAndInitHeap
justAllocator a = Cons (IMake justStru) $ Cons (ITag justTag) $ Cons (ISlot a) Nil

makeJust a cont = allocSlots (justAllocator a) cont


nothingTag = 2
nothingAllocator = Cons (IMake tagStru) $ Cons (ITag nothingTag) Nil
makeNothing cont = allocSlots nothingAllocator cont

singleObj = LLit $ Int 1

subPrimitive :: String -> [Exp] -> V -> FIOTermCont -> FIOTerm
subPrimitive "<" [a1, a2] _ cont = binaryPrimitive (Icmp OLt) i1 a1 a2 cont
subPrimitive "<=" [a1, a2] _ cont = binaryPrimitive (Icmp OLe) i1 a1 a2 cont
subPrimitive ">=" [a1, a2] _ cont = binaryPrimitive (Icmp OGe) i1 a1 a2 cont
subPrimitive ">" [a1, a2] _ cont = binaryPrimitive (Icmp OGt) i1 a1 a2 cont
subPrimitive "==" [a1, a2] _ cont = binaryPrimitive (Icmp OEq) i1 a1 a2 cont
subPrimitive "/=" [a1, a2] _ cont = binaryPrimitive (Icmp ONe) i1 a1 a2 cont

subPrimitive "+" [a1, a2] _ cont = binaryPrimitive Add i32 a1 a2 cont
subPrimitive "-" [a1, a2] _ cont = binaryPrimitive Sub i32 a1 a2 cont
subPrimitive "*" [a1, a2] _ cont = binaryPrimitive Mul i32 a1 a2 cont
subPrimitive "div" [a1, a2] _ cont = binaryPrimitive Div i32 a1 a2 cont

subPrimitive "Just" [arg] (Vprimfun "Just" f) cont = do
             subComp arg (\v -> makeJust v cont)

subPrimitive "Nothing" [] (Vprimfun "Nothing" f) cont = makeNothing cont

-- constructorPrimitive


subPrimitive prim args (Vprimfun s f) cont = fail ("cannot subPrimitive, Vprimfun: " ++ show prim ++ "   args: " ++ show args ++ "   s: " ++ s {-++ "   f: " ++ show f-})
subPrimitive prim args v cont = fail ("cannot subPrimitive: " ++ show prim ++ "   args: " ++ show args ++ "   v: " ++ show v)

binaryPrimitive :: (Value -> Value -> Instr Cabl Cabl) -> LType a
                -> Exp -> Exp -> FIOTermCont -> FIOTerm
binaryPrimitive former typ a1 a2 cont = do
                                       subComp a1 (\v1 -> do
                                                   subComp a2 (\v2 -> do
                                                               lab <- fresh
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
showThrist (Cons i@(Malloc t v) r) = do
                                    humpti <- showThrist r
                                    let elems (LLit (Int 1)) = ""
                                        elems _ = ", " ++ show v
                                    return (" malloc " ++ show t ++ elems v ++ "\n" ++ humpti)
showThrist (Cons i@(Store v p) r) = do
                                    humpti <- showThrist r
                                    return (" store " ++ show v ++ ", " ++ show p ++ "\n" ++ humpti)
showThrist (Cons i@(Load p) r) = do
                                    humpti <- showThrist r
                                    return (" load " ++ show p ++ "\n" ++ humpti)
showThrist (Cons (Phi fan) r) = do
                              humpti <- showThrist r
                              return (" phi " ++ show fan ++ "\n" ++ humpti)
showThrist (Cons (Switch v fan) r) = do
                              humpti <- showThrist r
                              let showFan (_, BB n thr) = do { thrText <- showThrist thr; return ("%" ++ show n ++ ": " ++ thrText) }
                              fans <- mapFIO showFan fan
                              return (" switch " ++ show v ++ " --> " ++ show fan ++ "\n" ++ concat fans ++ humpti)
showThrist (Cons (Branch (to@(BB _ thr))) r) = do
                              humpti <- showThrist r
                              taste <- showThrist thr
                              return (" branch " ++ show to ++ ";;; " ++ taste ++ "\n" ++ humpti)
showThrist (Cons (Gep t g v) r) = do
                              humpti <- showThrist r
                              return (" getelementpointer " ++ show v ++ showGup g ++ "\n" ++ humpti)
showThrist (Cons x r) = return "cannot showThrist"


-- forbidden gups:
-- g1 = Cons Drill $ Cons deref0 Nil

showGup :: Thrist Gup a b -> String
showGup Nil = ""
showGup (Cons (Deref offs) r) = ", " ++ show offs ++ showGup r
showGup (Cons Drill r) = ", " ++ show i32 ++ " " ++ show 0 ++ showGup r
showGup (Cons Skip r) = countdown 1 r
    where countdown :: Int -> Thrist Gup a b -> String
          countdown n (Cons Drill r) = ", " ++ show i32 ++ " " ++ show n ++ showGup r
          countdown n (Cons Skip r) = countdown (n + 1) r


showBinaryArithmetic :: String -> Value -> Value -> Instr a b -> Thrist Instr b Term -> FIO String
showBinaryArithmetic op v1 v2 _ r = do
                                    humpti <- showThrist r
                                    return (" " ++ op ++ " " ++ show v1 ++ " " ++ show v2 ++ "\n" ++ humpti)

instance Show Value where
  show (LLit (Int i)) = show i32 ++ " " ++ show i
  show (Undef t) = show t ++ " undef"
  show (Ref t l) = show t ++ " %" ++ show l
  show (Lab r) = "label %" ++ show r

instance Show BasicBlock where
  show (BB n _) = show (Lab n)


instance Show (LType a) where
  show (LInt i) = "i" ++ show i
  show (LPtr a) = show a ++ "*"
  show (LEmpty) = "{}"
  show (ext@(LExtend _ _)) = "{" ++ descend ext
      where descend :: LType (LStruct (b, c)) -> String
            descend (LExtend a LEmpty) = show a ++ "}"
            descend (LExtend a more@(LExtend _ _)) = show a ++ ", " ++ descend more
  show (LArray a d) = "[" ++ show a ++ " x " ++ show d ++ "]"
  show (LNamed t n) = "%" ++ show n
