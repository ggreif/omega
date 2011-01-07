
------------------------------------------
-- level polymorphism

prop Eqz:: level n. forall (t:: *(1+n)) .t ~> t ~> *0 where
  E :: Eqz a a

prop Eqw:: t ~> t ~> *0 where
  Ew :: Eqw a a


data Mx:: *1 where
 F :: Int ~> Mx



fe:: a -> Eqz a a
fe x = E

----------------------------------------------------

##test "level too low"  
 data Natural:: level n . *n  where
   Zero :: Natural
   Succ :: Natural ~> Natural
   D :: Int ~> Natural
  
data Natural:: level n . *n where
   Zero :: Natural 
   Succ :: Natural ~> Natural  
 deriving Nat(n) 

-- Singleton

data Natural' :: level n . Natural_(1) ~> *n where
  Zero' :: Natural' Zero
  Succ' :: Natural' n ~> Natural' (Succ n)
    deriving Nat(m)   

---------------------------------------------

data L:: level n . *n ~> *n where
   Nil :: L x
   Cons :: x ~> L x ~> L x
  deriving List(x)

data Bush:: level n . *n ~> *n where
   Fork:: L x ~> Bush x
  
data L2:: level n . (x:: *(n+1)) ~> *n where
   Nil2 :: L2 x
   Cons2 :: x ~> L2 x ~> L2 x   
      
  