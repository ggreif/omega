
data Operation:: *1 where
  Print:: Operation

data Object:: *1 where
  TheOutput:: Object  

data Action:: *1 where
  Act:: Nat ~> Operation ~> Object ~> Action

 
data Permission:: Action ~> *0 where 
  WriteOutput:: Nat' s -> Permission (Act s Print TheOutput)
----------------------------------------
data Seq:: *1 ~> *1 where
  Snil:: Seq a
  Scons:: a ~> Seq a ~> Seq a
   deriving List(s)  

app:: Seq a ~> Seq a ~> Seq a
{app (Scons x xs) ys} = Scons x {app xs ys}
{app Snil ys} = ys

----------------------------------

data Trace:: Seq Action ~> *0 where
  Lnil :: Trace Snil
  Lcons :: Permission x -> Trace xs -> Trace (Scons x xs)
 deriving List(l)  


-- Test unreachabilty by non-staifiablilty of predicates
unrByPred :: Trace a -> Equal {app a b} Snil -> (Equal a Snil,Equal b Snil)
unrByPred (x@Lnil) (p@Eq) = (Eq,Eq)
unrByPred (x@(Lcons x xs)) (p@Eq) = unreachable

-- Shows unreachable can't be spoofed
##test "Really is reachable"
 hh:: Trace a -> Trace a -> Trace a
 hh Lnil Lnil = unreachable
 hh Lnil (Lcons x xs) = Lnil

-- Test unreachability of patterns alone
unrByPat:: Trace a -> Trace a -> Trace a
unrByPat Lnil Lnil = Lnil
unrByPat Lnil (Lcons x xs) = unreachable

-- Test works on case statements as well 

unrByPatByCase:: Trace a -> Trace a -> Trace a
unrByPatByCase x y = case (x,y) of
  (Lnil,Lnil) -> Lnil
  (Lnil,Lcons x xs) -> unreachable

unrByPredCase :: Trace a -> Equal {app a b} Snil -> (Equal a Snil,Equal b Snil)
unrByPredCase x y = case (x,y) of
  (x@Lnil,p@Eq) -> (Eq,Eq)
  (x@(Lcons x xs),p@Eq) -> unreachable
