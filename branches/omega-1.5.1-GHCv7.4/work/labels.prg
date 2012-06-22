
labelEq :: Label a -> Label b -> Maybe(Equal a b)
labelEq x y = case sameLabel x y of
              L(t @ Eq) -> Just t
              R _ -> Nothing
              
(Just (proof @ Eq)) = labelEq `a `a

copy = `copy

test = HideLabel copy

HideLabel y = newLabel "x"
              
f x = case sameLabel y `a of
        L (t@Eq) -> t
        R _ -> error "BAD"
  where (HideLabel y) = newLabel x
  
type Env = [exists t .(Label t,Int)]

find:: Label t -> Env -> Maybe(Label t,Int)
find t [] = Nothing
find t ((Ex(s,n)):xs) = 
  case labelEq t s of
    Just (p@Eq) -> Just(t,n)
    Nothing -> find t xs 

testpairs :: Env    
testpairs = [gg(`a,2),gg(`b,3),gg(`c,99)]  
  
gg:: (Label a,Int) -> exists t .(Label t,Int)
gg (x,y) = Ex(x,y)

okSearch = case find `b testpairs of
        (Just (_,3)) -> True
        _ -> False

##test "labels not equal"
  (Just q) = labelEq `a `b
        
##test "label find search"
  notOkSearch = 
    case find `q testpairs of
     (Just (_,_)) -> error "We expect to fall off the case arms without matching"

